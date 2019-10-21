// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.script

import java.util
import scala.collection.JavaConverters._
import java.time.Instant
import akka.actor.ActorSystem
import akka.stream.scaladsl._
import akka.stream._
import scalaz.syntax.tag._

import java.util.UUID

import com.digitalasset.ledger.client.services.admin.PartyManagementClient
import com.digitalasset.ledger.api.v1.admin.party_management_service.PartyManagementServiceGrpc
import com.digitalasset.ledger.api.v1.event.{CreatedEvent}
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.concurrent.duration.Duration
import scalaz.syntax.traverse._

import com.digitalasset.ledger.api.validation.ValueValidator
import com.digitalasset.ledger.api.v1.transaction.TreeEvent
import com.digitalasset.daml.lf.archive.{Dar, DarReader}
import com.digitalasset.daml.lf.archive.Decode
import com.digitalasset.daml.lf.data.FrontStack
import com.digitalasset.daml.lf.data.Ref.{ContractIdString, DottedName, Identifier, Name, PackageId, QualifiedName}
import com.digitalasset.daml.lf.language.Ast.Package
import com.digitalasset.daml_lf_dev.DamlLf
import com.digitalasset.grpc.adapter.AkkaExecutionSequencerPool
import com.digitalasset.ledger.api.domain.LedgerId
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
import com.digitalasset.daml.lf.speedy.{Speedy, SValue, SExpr}
import com.digitalasset.daml.lf.speedy.Pretty
import com.digitalasset.daml.lf.speedy.SExpr._
import com.digitalasset.daml.lf.speedy.SResult._
import com.digitalasset.daml.lf.speedy.SValue._
import com.digitalasset.daml.lf.speedy.SBuiltin._

import com.digitalasset.ledger.api.v1.value.{Identifier => ApiIdentifier}
import com.digitalasset.ledger.api.v1.command_service.SubmitAndWaitRequest
import com.digitalasset.ledger.api.v1.commands._
import com.digitalasset.ledger.api.v1.transaction_filter.{Filters, TransactionFilter, InclusiveFilters}

import com.digitalasset.api.util.TimestampConversion.fromInstant
import com.digitalasset.platform.participant.util.LfEngineToApi.{
  toApiIdentifier,
  lfValueToApiRecord,
  lfValueToApiValue
}

import com.digitalasset.daml.lf.value.Value.{AbsoluteContractId, RelativeContractId}

import io.grpc.Channel

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
        implicit val materializer: ActorMaterializer = ActorMaterializer()(system)

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

        def getApFields(fun : SValue) : (SVariant, SVariant) = {
          val extractTuple = SEMakeClo(Array(), 2, SEApp(SEBuiltin(SBTupleCon(Name.Array(Name.assertFromString("a"), Name.assertFromString("b")))), Array(SEVar(2), SEVar(1))))
          val machine = Speedy.Machine.fromSExpr(SEApp(SEValue(fun), Array(extractTuple)), false, compiledPackages)
          while (!machine.isFinal) {
            machine.step() match {
              case SResultContinue => ()
              case res => {
                throw new RuntimeException(s"Unexpected speedy result $res")
              }
            }
          }
          val tuple = machine.toSValue.asInstanceOf[STuple]
          (tuple.values.get(0).asInstanceOf[SVariant], tuple.values.get(1).asInstanceOf[SVariant])
        }

        def toCreateCommand(v : SRecord) : Command = {
          val anyTemplate = v.values.get(0).asInstanceOf[SRecord].values.get(0).asInstanceOf[SAny]
          val templateTy = anyTemplate.ty.asInstanceOf[TTyCon].tycon
          val templateArg = anyTemplate.value
          Command().withCreate(
            CreateCommand(
              Some(toApiIdentifier(templateTy)),
              Some(toLedgerRecord(templateArg).right.get)))
        }

        def toIdentifier(v : SRecord) : ApiIdentifier = {
          val tId = v.values.get(0).asInstanceOf[SText].value
          val packageId = tId.split('(')(1).split(',')(0)
          val moduleId = tId.split(',')(1).split(')')(0).split(':')(0)
          val entityId = tId.split(',')(1).split(')')(0).split(':')(1)
          ApiIdentifier(packageId, moduleId, entityId)
        }

        def toExerciseCommand(v : SRecord) : Command = {
          val tplId = toIdentifier(v.values.get(0).asInstanceOf[SRecord])
          val cId = v.values.get(1).asInstanceOf[SContractId].value.asInstanceOf[AbsoluteContractId].coid
          val anyChoice = v.values.get(2).asInstanceOf[SRecord].values.get(0).asInstanceOf[SAny]
          val anyChoiceVal = anyChoice.value
          val choiceName = anyChoiceVal.asInstanceOf[SRecord].id.qualifiedName.name.toString
          Command().withExercise(
            ExerciseCommand(
              Some(tplId),
              cId,
              choiceName,
              Some(toLedgerValue(anyChoiceVal).right.get)))
        }

        def toSubmitRequest(ledgerId: LedgerId, party: SParty, cmds: Seq[Command]) = {
          val commands = Commands(
            party = party.value,
            commands = cmds,
            ledgerId = ledgerId.unwrap,
            applicationId = applicationId.unwrap,
            commandId = UUID.randomUUID.toString,
            ledgerEffectiveTime = Some(fromInstant(Instant.EPOCH)),
            maximumRecordTime = Some(fromInstant(Instant.EPOCH.plusSeconds(5)))
          )
          SubmitAndWaitRequest(Some(commands))
        }

        def getCommands(initialFreeAp: SVariant) : Seq[Command] = {
          var end = false
          var commands = Seq[Command]()
          val pure = Name.assertFromString("PureA")
          val ap = Name.assertFromString("Ap")
          var freeAp = initialFreeAp
          do {
            freeAp.variant match {
              case `pure` => {
                end = true
              }
              case `ap` => {
                val (fa, apfba) = getApFields(freeAp.value)
                fa.variant match {
                  case "Create" =>
                    commands ++= Seq(toCreateCommand(fa.value.asInstanceOf[SRecord]))
                  case "Exercise" =>
                    commands ++= Seq(toExerciseCommand(fa.value.asInstanceOf[SRecord]))
                  case _ => throw new RuntimeException("Unknown command: ${fa.variant}")
                }
                freeAp = apfba
              }
            }
          } while (!end)
          commands
        }

        def fillCommandResults(freeAp: SVariant, eventResults: Seq[TreeEvent]) : SExpr = {
          val pure = Name.assertFromString("PureA")
          val ap = Name.assertFromString("Ap")
          freeAp.variant match {
            case `pure` => SEValue(freeAp.value)
            case `ap` => {
              val (fa, apfba) = getApFields(freeAp.value)
              val bValue = fa.variant match {
                case "Create" => {
                  val continue = fa.value.asInstanceOf[SRecord].values.get(1)
                  val contractIdString = eventResults.head.getCreated.contractId
                  val contractId =
                    SContractId(AbsoluteContractId(ContractIdString.assertFromString(contractIdString)))
                  SEApp(SEValue(continue), Array(SEValue(contractId)))
                }
                case "Exercise" => {
                  val continue = fa.value.asInstanceOf[SRecord].values.get(3)
                  val apiExerciseResult = eventResults.head.getExercised.getExerciseResult
                  val exerciseResult =
                    SValue.fromValue(ValueValidator.validateValue(apiExerciseResult).right.get)
                  SEApp(SEValue(continue), Array(SEValue(exerciseResult)))
                }
                case _ => throw new RuntimeException("Unknown command: ${fa.variant}")
              }
              val fValue = fillCommandResults(apfba, eventResults.tail)
              SEApp(fValue, Array(bValue))
            }

          }
        }

        def run(channel : Channel, client: LedgerClient) = {
          val partyClient = new PartyManagementClient(PartyManagementServiceGrpc.stub(channel))
          val scriptExpr = EVal(scriptId)
          val machine = Speedy.Machine.fromSExpr(compiler.compile(scriptExpr), false, compiledPackages)
          var end = false
          println("Starting DAML script")
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
            machine.traceLog.iterator.foreach {
              case (msg, optLoc) =>
                println(s"TRACE ${Pretty.prettyLoc(optLoc).render(80)}: $msg")
            }
            machine.toSValue match {
              case SVariant(_, constr, v) =>
                if (constr.equals(Name.assertFromString("Free"))) {
                  v match {
                    case SVariant(_, constr, v) => {
                      if (constr == Name.assertFromString("Submit")) {
                        v match {
                          case SRecord(_, _, vals) => {
                            assert(vals.size == 2)
                            val party = vals.get(0).asInstanceOf[SParty]
                            val freeAp = vals.get(1).asInstanceOf[SVariant]
                            val commands = getCommands(freeAp)
                            val request = toSubmitRequest(client.ledgerId, party, commands)
                            val f = client.commandServiceClient.submitAndWaitForTransactionTree(request)
                            val transactionTree = Await.result(f, Duration.Inf).getTransaction
                            val events =
                              transactionTree.rootEventIds.map(evId => transactionTree.eventsById(evId))
                            val filled = fillCommandResults(freeAp, events)
                            machine.ctrl = Speedy.CtrlExpr(filled)
                          }
                          case _ => throw new RuntimeException(s"Expected record but got $v")
                        }
                      } else if (constr == Name.assertFromString("Query")) {
                        v match {
                          case SRecord(_, _, vals) => {
                            assert(vals.size == 3)
                            val party = vals.get(0).asInstanceOf[SParty].value
                            val tplId = toIdentifier(vals.get(1).asInstanceOf[SRecord])
                            val continue = vals.get(2)
                            val filter = TransactionFilter(List(
                              (party, Filters(Some(InclusiveFilters(Seq(tplId)))))).toMap)
                            val anyTemplateTyCon =
                              Identifier(
                                stdlibPackageId,
                                QualifiedName(
                                  DottedName.assertFromString("DA.Internal.LF"),
                                  DottedName.assertFromString("AnyTemplate")))
                            def record(ty: Identifier, fields: (String, SValue)*): SValue = {
                              val fieldNames = Name.Array(fields.map({ case (n, _) => Name.assertFromString(n) }): _*)
                              val args = new util.ArrayList[SValue](fields.map({ case (_, v) => v }).asJava)
                              SRecord(ty, fieldNames, args)
                            }
                            def fromCreated(created: CreatedEvent) = {
                              val arg = SValue.fromValue(ValueValidator.validateRecord(created.getCreateArguments).right.get)
                              val tyCon = arg.asInstanceOf[SRecord].id
                              record(anyTemplateTyCon, ("getAnyTemplate", SAny(TTyCon(tyCon), arg)))
                            }
                            val acsResponses = client.activeContractSetClient
                              .getActiveContracts(filter, verbose = true)
                              .runWith(Sink.seq)
                            val res = Await.result(acsResponses, Duration.Inf)
                              .flatMap(x => x.activeContracts)
                              .map(fromCreated)
                            machine.ctrl = Speedy.CtrlExpr(SEApp(SEValue(continue), Array(SEValue(SList(FrontStack(res))))))

                          }
                          case _ => throw new RuntimeException(s"Expected record but got $v")
                        }
                      } else if (constr == Name.assertFromString("AllocParty")) {
                        v match {
                          case SRecord(_, _, vals) => {
                            assert(vals.size == 2)
                            val displayName = vals.get(0).asInstanceOf[SText].value
                            val f = partyClient.allocateParty(None, Some(displayName))
                            val party = Await.result(f, Duration.Inf).party
                            val continue = vals.get(1)
                            machine.ctrl = Speedy.CtrlExpr(SEApp(SEValue(continue), Array(SEValue(SParty(party)))))
                          }
                          case _ => throw new RuntimeException(s"Expected record but got $v")
                        }
                      } else {
                        throw new RuntimeException(s"Unknown constructor: $constr")
                      }
                    }
                    case _ => throw new RuntimeException(s"Expected variant")
                  }
                } else {
                  end = true
                }
              case v => throw new RuntimeException(s"Expected variant")
            }
          }
        }
        val channel = LedgerClient.constructChannel(config.ledgerHost, config.ledgerPort, clientConfig)
        val flow: Future[Unit] = for {
          client <- LedgerClient.forChannel(clientConfig, channel)(ec, sequencer)
          _ = run(channel, client)
        } yield ()

        flow.onComplete(_ => system.terminate())
        Await.result(flow, Duration.Inf)
      }
    }
  }
}
