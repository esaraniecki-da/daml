// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.script

import java.time.Instant
import akka.actor.ActorSystem
import scalaz.syntax.tag._

import java.util.UUID

import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration.Duration
import scalaz.syntax.traverse._

import com.digitalasset.ledger.api.validation.ValueValidator
import com.digitalasset.daml.lf.archive.{Dar, DarReader}
import com.digitalasset.daml.lf.archive.Decode
import com.digitalasset.daml.lf.data.Ref.{DottedName, Identifier, Name, PackageId, QualifiedName, ContractIdString}
import com.digitalasset.daml.lf.language.Ast.Package
import com.digitalasset.daml_lf_dev.DamlLf
import com.digitalasset.grpc.adapter.AkkaExecutionSequencerPool
import com.digitalasset.ledger.api.refinements.ApiTypes.ApplicationId
import com.digitalasset.ledger.client.LedgerClient
import com.digitalasset.ledger.client.configuration.{
  CommandClientConfiguration,
  LedgerClientConfiguration,
  LedgerIdRequirement
}

import com.digitalasset.daml.lf.language.Ast._
import com.digitalasset.daml.lf.PureCompiledPackages
import com.digitalasset.daml.lf.speedy.Compiler
import com.digitalasset.daml.lf.speedy.{Speedy, SValue}
import com.digitalasset.daml.lf.speedy.SExpr._
import com.digitalasset.daml.lf.speedy.SResult._
import com.digitalasset.daml.lf.speedy.SValue._

import com.digitalasset.ledger.api.v1.event._
import com.digitalasset.ledger.api.v1.value.{Identifier => ApiIdentifier}
import com.digitalasset.ledger.api.v1.command_service.SubmitAndWaitRequest
import com.digitalasset.ledger.api.v1.commands.{Command, Commands, CreateCommand, ExerciseCommand}

import com.digitalasset.api.util.TimestampConversion.fromInstant
import com.digitalasset.platform.participant.util.LfEngineToApi.{
  toApiIdentifier,
  lfValueToApiRecord,
  lfValueToApiValue
}

import com.digitalasset.daml.lf.value.Value.{AbsoluteContractId, RelativeContractId}

object RunnerMain {

  def main(args: Array[String]): Unit = {

    RunnerConfig.parse(args) match {
      case None => sys.exit(1)
      case Some(config) => {
        val encodedDar: Dar[(PackageId, DamlLf.ArchivePayload)] =
          DarReader().readArchiveFromFile(config.darPath).get
        val dar: Dar[(PackageId, Package)] = encodedDar.map {
          case (pkgId, pkgArchive) => Decode.readArchivePayload(pkgId, pkgArchive)
        }

        val scriptModuleName = DottedName.assertFromString("Daml.Script")

        val scriptId: Identifier =
          Identifier(dar.main._1, QualifiedName.assertFromString(config.scriptIdentifier))

        val scriptPackageId: PackageId = dar.all
          .find {
            case (pkgId, pkg) => pkg.modules.contains(scriptModuleName)
          }
          .get
          ._1
        val stdlibPackageId =
          dar.all
            .find {
              case (pkgId, pkg) =>
                pkg.modules.contains(DottedName.assertFromString("DA.Internal.LF"))
            }
            .get
            ._1

        val applicationId = ApplicationId("Script Runner")
        val clientConfig = LedgerClientConfiguration(
          applicationId = ApplicationId.unwrap(applicationId),
          ledgerIdRequirement = LedgerIdRequirement("", enabled = false),
          commandClient = CommandClientConfiguration.default,
          sslContext = None
        )

        val system: ActorSystem = ActorSystem("ScriptRunner")
        val sequencer = new AkkaExecutionSequencerPool("ScriptRunnerPool")(system)
        implicit val ec: ExecutionContext = system.dispatcher

        val darMap: Map[PackageId, Package] = dar.all.toMap
        val compiler = Compiler(darMap)
        // We overwrite the definition of toLedgerValue with an identity function.
        // This is a type error but Speedy doesn’t care about the types and the only thing we do
        // with the result is convert it to ledger values/record so this is safe.
        val definitionMap =
          compiler.compilePackages(darMap.keys) +
        (LfDefRef(
          Identifier(
            scriptPackageId,
            QualifiedName(
              scriptModuleName,
              DottedName.assertFromString("fromLedgerValue")))) ->
          SEMakeClo(Array(), 1, SEVar(1)))
        val compiledPackages = PureCompiledPackages(darMap, definitionMap).right.get

        def toLedgerRecord(v: SValue) = {
          lfValueToApiRecord(
            true,
            v.toValue.mapContractId {
              case rcoid: RelativeContractId =>
                throw new RuntimeException(s"Unexpected contract id $rcoid")
              case acoid: AbsoluteContractId => acoid
            }
          )
        }

        def toLedgerValue(v: SValue) = {
          lfValueToApiValue(
            true,
            v.toValue.mapContractId {
              case rcoid: RelativeContractId =>
                throw new RuntimeException(s"Unexpected contract id $rcoid")
              case acoid: AbsoluteContractId => acoid
            }
          )
        }


        def run(client: LedgerClient) = {
          val scriptExpr = EVal(scriptId)
          val machine = Speedy.Machine.fromSExpr(compiler.compile(scriptExpr), false, compiledPackages)
          var end = false
          while (!end) {
            while (!machine.isFinal) {
              machine.step() match {
                case SResultContinue => ()
                case SResultError(err) => {
                  throw new RuntimeException(err)
                }
                case res => {
                  throw new RuntimeException(s"Unexpected speedy result $res")
                }
              }
            }
            machine.toSValue match {
              case SVariant(_, constr, v) =>
                if (constr.equals(Name.assertFromString("Free"))) {
                  v match {
                    case SVariant(_, constr, v) => {
                      if (constr == Name.assertFromString("Create")) {
                        v match {
                          case SRecord(_, _, vals) => {
                            assert(vals.size == 3)
                            val party = vals.get(0).asInstanceOf[SParty].value
                            val anyTemplate = vals.get(1).asInstanceOf[SRecord].values.get(0).asInstanceOf[SAny]
                            val templateTy = anyTemplate.ty.asInstanceOf[TTyCon].tycon
                            val templateArg = anyTemplate.value
                            val continue = vals.get(2)
                            val command = Command().withCreate(CreateCommand(Some(toApiIdentifier(templateTy)), Some(toLedgerRecord(templateArg).right.get)))
                            val commands = Commands(
                              ledgerId = client.ledgerId.unwrap,
                              applicationId = ApplicationId.unwrap(applicationId),
                              commandId = UUID.randomUUID.toString,
                              ledgerEffectiveTime = Some(fromInstant(Instant.EPOCH)),
                              maximumRecordTime = Some(fromInstant(Instant.EPOCH.plusSeconds(5))),
                              party = party,
                              commands = Seq(command)
                            )
                            val f = client.commandServiceClient.submitAndWaitForTransaction(SubmitAndWaitRequest(commands = Some(commands)))
                            val transaction = Await.result(f, Duration.Inf).getTransaction
                            val contractId = transaction.events(0).getCreated.asInstanceOf[CreatedEvent].contractId
                            machine.ctrl = Speedy.CtrlExpr(SEApp(SEValue(continue), Array(SEValue(SContractId(AbsoluteContractId(ContractIdString.assertFromString(contractId)))))))
                          }
                          case _ => throw new RuntimeException(s"Expected record but got $v")
                        }
                      } else if (constr == Name.assertFromString("Exercise")) {
                        v match {
                          case SRecord(_, _, vals) => {
                            assert(vals.size == 5)
                            val party = vals.get(0).asInstanceOf[SParty].value
                            val tId = vals.get(1).asInstanceOf[SRecord].values.get(0).asInstanceOf[SText].value
                            val packageId = tId.split('(')(1).split(',')(0)
                            val moduleId = tId.split(',')(1).split(')')(0).split(':')(0)
                            val entityId = tId.split(',')(1).split(')')(0).split(':')(1)
                            val tplId = ApiIdentifier(packageId, moduleId, entityId)
                            val cId = vals.get(2).asInstanceOf[SContractId].value.asInstanceOf[AbsoluteContractId].coid
                            val anyChoice = vals.get(3).asInstanceOf[SRecord].values.get(0).asInstanceOf[SAny]
                            val anyChoiceVal = anyChoice.value
                            val valChoiceName = anyChoiceVal.asInstanceOf[SRecord].id.qualifiedName.name.toString
                            val continue = vals.get(4)
                            val command = Command().withExercise(ExerciseCommand(Some(tplId), cId, valChoiceName, Some(toLedgerValue(anyChoiceVal).right.get)))
                            val commands = Commands(
                              ledgerId = client.ledgerId.unwrap,
                              applicationId = ApplicationId.unwrap(applicationId),
                              commandId = UUID.randomUUID.toString,
                              ledgerEffectiveTime = Some(fromInstant(Instant.EPOCH)),
                              maximumRecordTime = Some(fromInstant(Instant.EPOCH.plusSeconds(5))),
                              party = party,
                              commands = Seq(command)
                            )
                            val f = client.commandServiceClient.submitAndWaitForTransactionTree(SubmitAndWaitRequest(commands = Some(commands)))
                            val transactionTree = Await.result(f, Duration.Inf).getTransaction
                            val exerciseResult = transactionTree.eventsById(transactionTree.rootEventIds(0)).getExercised.getExerciseResult
                            val exerciseVal = SValue.fromValue(ValueValidator.validateValue(exerciseResult).right.get)
                            machine.ctrl = Speedy.CtrlExpr(SEApp(SEValue(continue), Array(SEValue(exerciseVal))))
                          }
                          case _ => throw new RuntimeException(s"Expected record but got $v")
                        }
                      } else {
                        throw new RuntimeException(s"Unknown constructor: $constr")
                      }
                    }
                    case _ => throw new RuntimeException(s"Expected variant but got $v")
                  }
                } else {
                  end = true
                }
              case v => throw new RuntimeException(s"Expected variant but got $v")
            }
          }
        }

        val flow: Future[Unit] = for {
          client <- LedgerClient.singleHost(config.ledgerHost, config.ledgerPort, clientConfig)(
            ec,
            sequencer)
          _ = run(client)
        } yield ()

        flow.onComplete(_ => system.terminate())
        Await.result(flow, Duration.Inf)
      }
    }
  }
}
