// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.platform.tests.integration.ledger.api

import java.io.File
import java.nio.file.Files
import java.util.{Timer, TimerTask, UUID}

import com.digitalasset.daml.bazeltools.BazelRunfiles.rlocation
import com.digitalasset.jwt.{HMAC256Verifier, JwtSigner}
import com.digitalasset.jwt.domain.DecodedJwt
import com.digitalasset.ledger.api.auth.{AuthServiceJWT, AuthServiceJWTCodec, AuthServiceJWTPayload}
import com.digitalasset.ledger.api.domain.LedgerId
import com.digitalasset.ledger.api.testing.utils.{
  AkkaBeforeAndAfterAll,
  SuiteResourceManagementAroundAll
}
import com.digitalasset.ledger.api.v1.active_contracts_service.{
  GetActiveContractsRequest,
  GetActiveContractsResponse
}
import com.digitalasset.ledger.api.v1.admin.package_management_service.{
  ListKnownPackagesRequest,
  UploadDarFileRequest
}
import com.digitalasset.ledger.api.v1.admin.party_management_service.{
  AllocatePartyRequest,
  ListKnownPartiesRequest
}
import com.digitalasset.ledger.api.v1.command_completion_service.{
  CompletionEndRequest,
  CompletionStreamRequest,
  CompletionStreamResponse
}
import com.digitalasset.ledger.api.v1.command_service.SubmitAndWaitRequest
import com.digitalasset.ledger.api.v1.ledger_configuration_service.{
  GetLedgerConfigurationRequest,
  GetLedgerConfigurationResponse
}
import com.digitalasset.ledger.api.v1.ledger_identity_service.GetLedgerIdentityRequest
import com.digitalasset.ledger.api.v1.ledger_offset.LedgerOffset
import com.digitalasset.ledger.api.v1.testing.time_service.{GetTimeRequest, GetTimeResponse}
import com.digitalasset.ledger.api.v1.transaction_filter.{Filters, TransactionFilter}
import com.digitalasset.ledger.api.v1.transaction_service.{
  GetLedgerEndRequest,
  GetTransactionByEventIdRequest,
  GetTransactionByIdRequest,
  GetTransactionTreesResponse,
  GetTransactionsRequest,
  GetTransactionsResponse
}
import com.digitalasset.platform.apitesting.{
  Header,
  LedgerContext,
  MultiLedgerFixture,
  TestCommands,
  TestIdsGenerator
}
import com.google.protobuf.ByteString
import io.grpc.{Status, StatusException, StatusRuntimeException}
import io.grpc.stub.StreamObserver
import org.scalatest.concurrent.AsyncTimeLimitedTests
import org.scalatest.{AsyncWordSpec, Matchers}

import scala.concurrent.{Future, Promise}
import scalaz.syntax.tag._

class AuthorizationIT
    extends AsyncWordSpec
    with AkkaBeforeAndAfterAll
    with MultiLedgerFixture
    with SuiteResourceManagementAroundAll
    with AsyncTimeLimitedTests
    with Matchers {

  protected val testCommands = new TestCommands(config)
  protected val testIdsGenerator = new TestIdsGenerator(config)

  private val operator = testIdsGenerator.testPartyName("Operator")
  private val alice = testIdsGenerator.testPartyName("Alice")
  private val bob = testIdsGenerator.testPartyName("Bob")

  private val operatorPayload = AuthServiceJWTPayload(
    ledgerId = None,
    participantId = None,
    applicationId = None,
    exp = None,
    admin = true,
    actAs = List(operator),
    readAs = List(operator)
  )

  private val alicePayload = AuthServiceJWTPayload(
    ledgerId = None,
    participantId = None,
    applicationId = None,
    exp = None,
    admin = false,
    actAs = List(alice),
    readAs = List(alice)
  )

  private val bobPayload = AuthServiceJWTPayload(
    ledgerId = None,
    participantId = None,
    applicationId = None,
    exp = None,
    admin = false,
    actAs = List(bob),
    readAs = List(bob)
  )

  private val jwtHeader = """{"alg": "HS256", "typ": "JWT"}"""
  private def jwtSecret = "AuthorizationIT"

  private val operatorToken = JwtSigner.HMAC256
    .sign(DecodedJwt(jwtHeader, AuthServiceJWTCodec.compactPrint(operatorPayload)), jwtSecret)
    .getOrElse(sys.error("Failed to generate token"))
    .value
  private val aliceToken = JwtSigner.HMAC256
    .sign(DecodedJwt(jwtHeader, AuthServiceJWTCodec.compactPrint(alicePayload)), jwtSecret)
    .getOrElse(sys.error("Failed to generate token"))
    .value
  private val bobToken = JwtSigner.HMAC256
    .sign(DecodedJwt(jwtHeader, AuthServiceJWTCodec.compactPrint(bobPayload)), jwtSecret)
    .getOrElse(sys.error("Failed to generate token"))
    .value
  private val invalidSignatureToken = JwtSigner.HMAC256
    .sign(
      DecodedJwt(jwtHeader, AuthServiceJWTCodec.compactPrint(operatorPayload)),
      "invalid secret")
    .getOrElse(sys.error("Failed to generate token"))
    .value

  private val operatorHeader = s"Bearer $operatorToken"
  private val aliceHeader = s"Bearer $aliceToken"
  private val bobHeader = s"Bearer $bobToken"
  private val invalidSignatureHeader = s"Bearer $invalidSignatureToken"

  private val testApplicationId = "AuthorizationIT"

  override protected def config: Config =
    Config.default
      .withAuthService(
        AuthServiceJWT(
          HMAC256Verifier(jwtSecret)
            .getOrElse(sys.error("Failed to create HMAC256 verifier"))))

  "ActiveContractsService" when {
    "getActiveContracts" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId.unwrap
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxBob = ctxNone.withAuthorizationHeader(Header(bob))

        def call(ctx: LedgerContext, party: String) =
          streamResult[GetActiveContractsResponse](
            observer =>
              ctx.acsService.getActiveContracts(
                new GetActiveContractsRequest(ledgerId, txFilterFor(party)),
                observer))

        for {
          _ <- mustBeDenied(call(ctxNone, alice)) // Reading the ACS for Alice without authorization
          _ <- mustBeDenied(call(ctxBob, alice)) // Reading the ACS for Alice as Bob
          _ <- call(ctxAlice, alice) // Reading the ACS for Alice as Alice
          _ <- mustBeDenied(call(ctxAliceExpired, alice)) // Reading the ACS for Alice as Alice after expiration
          _ <- call(ctxAliceValid, alice) // Reading the ACS for Alice as Alice before expiration
        } yield {
          succeed
        }
      }
    }
  }

  "CommandCompletionService" when {
    "completionEnd" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId.unwrap
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)

        def call(ctx: LedgerContext) =
          ctx.commandCompletionService.completionEnd(new CompletionEndRequest(ledgerId))

        for {
          _ <- mustBeDenied(call(ctxNone)) // Reading completion end without authorization
          _ <- mustBeDenied(call(ctxAliceExpired)) // Reading completion end with expired authorization
          _ <- call(ctxAlice) // Reading completion end with authorization
        } yield {
          succeed
        }
      }
    }
    "completionStream" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxBob = ctxNone.withAuthorizationHeader(Header(bob))

        def call(ctx: LedgerContext, party: String) =
          streamResult[CompletionStreamResponse](
            observer =>
              ctx.commandCompletionService.completionStream(
                new CompletionStreamRequest(
                  ledgerId.unwrap,
                  testApplicationId,
                  List(party),
                  Some(ledgerBegin)),
                observer))

        def callAndExpectExpiration(ctx: LedgerContext, party: String) =
          expectExpiration[CompletionStreamResponse](
            observer =>
              ctx.commandCompletionService.completionStream(
                new CompletionStreamRequest(
                  ledgerId.unwrap,
                  testApplicationId,
                  List(party),
                  Some(ledgerBegin)),
                observer))

        def scheduleCommandInMillis(millis: Long): Unit = {
          val timer = new Timer(true)
          timer.schedule(new TimerTask {
            override def run(): Unit = {
              val _ = ctxAlice.commandSubmissionService.submit(dummyCommandRequest(ledgerId, alice))
            }
          }, millis)
        }

        for {
          // Create some commands so that the completion stream is not empty
          _ <- ctxAlice.commandSubmissionService.submit(dummyCommandRequest(ledgerId, alice))

          _ <- mustBeDenied(call(ctxNone, alice)) // Reading completions for Alice without authorization
          _ <- mustBeDenied(call(ctxBob, alice)) // Reading completions for Alice as Bob
          _ <- call(ctxAlice, alice) // Reading completions for Alice as Alice
          _ <- mustBeDenied(call(ctxAliceExpired, alice)) // Reading completions for Alice as Alice after expiration
          _ <- call(ctxAliceValid, alice) // Reading completions for Alice as Alice before expiration
          _ = scheduleCommandInMillis(1100)
          ctxAliceAboutToExpire = ctxNone.withAuthorizationHeader(Header(alice).expiresInOneSecond)
          _ <- callAndExpectExpiration(ctxAliceAboutToExpire, alice)
        } yield {
          succeed
        }
      }
    }
  }

  "CommandService" when {
    "submitAndWait" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxBob = ctxNone.withAuthorizationHeader(Header(bob))

        def call(ctx: LedgerContext, party: String) =
          ctx.commandService.submitAndWait(dummySubmitAndWaitRequest(ledgerId, party))

        for {
          _ <- mustBeDenied(call(ctxNone, alice)) // Submitting commands for Alice without authorization
          _ <- mustBeDenied(call(ctxBob, alice)) // Submitting commands for Alice as Bob
          _ <- call(ctxAlice, alice) // Submitting commands for Alice as Alice
          _ <- mustBeDenied(call(ctxAliceExpired, alice)) // Submitting commands for Alice as Alice after expiration
          _ <- call(ctxAliceValid, alice) // Submitting commands for Alice as Alice before expiration
        } yield {
          succeed
        }
      }
    }
    "submitAndWaitForTransaction" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxBob = ctxNone.withAuthorizationHeader(Header(bob))

        def call(ctx: LedgerContext, party: String) =
          ctx.commandService.submitAndWaitForTransaction(dummySubmitAndWaitRequest(ledgerId, party))

        for {
          _ <- mustBeDenied(call(ctxNone, alice)) // Submitting commands for Alice without authorization
          _ <- mustBeDenied(call(ctxBob, alice)) // Submitting commands for Alice as Bob
          _ <- call(ctxAlice, alice) // Submitting commands for Alice as Alice
          _ <- mustBeDenied(call(ctxAliceExpired, alice))
          _ <- call(ctxAliceValid, alice)
        } yield {
          succeed
        }
      }
    }
    "submitAndWaitForTransactionId" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxBob = ctxNone.withAuthorizationHeader(Header(bob))

        def call(ctx: LedgerContext, party: String) =
          ctx.commandService.submitAndWaitForTransactionId(
            dummySubmitAndWaitRequest(ledgerId, party))

        for {
          _ <- mustBeDenied(call(ctxNone, alice)) // Submitting commands for Alice without authorization
          _ <- mustBeDenied(call(ctxBob, alice)) // Submitting commands for Alice as Bob
          _ <- call(ctxAlice, alice) // Submitting commands for Alice as Alice
          _ <- mustBeDenied(call(ctxAliceExpired, alice))
          _ <- call(ctxAliceValid, alice)
        } yield {
          succeed
        }
      }
    }
    "submitAndWaitForTransactionTree" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxBob = ctxNone.withAuthorizationHeader(Header(bob))

        def call(ctx: LedgerContext, party: String) =
          ctx.commandService.submitAndWaitForTransactionTree(
            dummySubmitAndWaitRequest(ledgerId, party))

        for {
          _ <- mustBeDenied(call(ctxNone, alice)) // Submitting commands for Alice without authorization
          _ <- mustBeDenied(call(ctxBob, alice)) // Submitting commands for Alice as Bob
          _ <- call(ctxAlice, alice) // Submitting commands for Alice as Alice
          _ <- mustBeDenied(call(ctxAliceExpired, alice))
          _ <- call(ctxAliceValid, alice)
        } yield {
          succeed
        }
      }
    }
  }

  "CommandSubmissionService" when {
    "submit" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxBob = ctxNone.withAuthorizationHeader(Header(bob))

        def call(ctx: LedgerContext, party: String) =
          ctx.commandSubmissionService.submit(dummyCommandRequest(ledgerId, party))

        for {
          _ <- mustBeDenied(call(ctxNone, alice)) // Submitting commands for Alice without authorization
          _ <- mustBeDenied(call(ctxBob, alice)) // Submitting commands for Alice as Bob
          _ <- call(ctxAlice, alice) // Submitting commands for Alice as Alice
          _ <- mustBeDenied(call(ctxAliceExpired, alice))
          _ <- call(ctxAliceValid, alice)
        } yield {
          succeed
        }
      }
    }
  }

  "LedgerConfigurationService" when {
    "getLedgerConfiguration" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId.unwrap
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)

        def call(ctx: LedgerContext) =
          streamResult[GetLedgerConfigurationResponse](
            observer =>
              ctx.ledgerConfigurationService
                .getLedgerConfiguration(new GetLedgerConfigurationRequest(ledgerId), observer)
          )

        for {
          _ <- mustBeDenied(call(ctxNone)) // Reading the ledger configuration without authorization
          _ <- call(ctxAlice) // Reading the ledger configuration with authorization
          _ <- mustBeDenied(call(ctxAliceExpired))
          _ <- call(ctxAliceValid)
        } yield {
          succeed
        }
      }
    }
  }

  "LedgerIdentityService" when {
    "getLedgerIdentity" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxAliceInvalidSignature = ctxNone.withAuthorizationHeader(Header(invalidSignatureHeader))

        def call(ctx: LedgerContext) =
          ctx.ledgerIdentityService.getLedgerIdentity(new GetLedgerIdentityRequest())

        for {
          _ <- mustBeDenied(call(ctxNone)) // Reading the ledger ID without authorization
          _ <- mustBeDenied(call(ctxAliceInvalidSignature)) // Reading the ledger ID with an invalid token
          _ <- call(ctxAlice) // Reading the ledger ID with authorization
          _ <- mustBeDenied(call(ctxAliceExpired))
          _ <- call(ctxAliceValid)
        } yield {
          succeed
        }
      }
    }
  }

  "PackageManagementService" when {
    "listKnownPackages" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAdmin = ctxNone.withAuthorizationHeader(Header(operator))
        val ctxAdminExpired = ctxNone.withAuthorizationHeader(Header(operator).expired)
        val ctxAdminValid = ctxNone.withAuthorizationHeader(Header(operator).expiresTomorrow)

        def call(ctx: LedgerContext) =
          ctx.packageManagementService.listKnownPackages(new ListKnownPackagesRequest())

        for {
          _ <- mustBeDenied(call(ctxNone)) // Listing packages without authorization
          _ <- mustBeDenied(call(ctxAlice)) // Listing packages as Alice (a regular user)
          _ <- call(ctxAdmin) // Listing packages as Operator (an admin)
          _ <- mustBeDenied(call(ctxAdminExpired))
          _ <- call(ctxAdminValid)
        } yield {
          succeed
        }
      }
    }
    "uploadDarFile" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val darFile =
          Files.readAllBytes(new File(rlocation("ledger/test-common/Test-stable.dar")).toPath)

        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAdmin = ctxNone.withAuthorizationHeader(Header(operator))
        val ctxAdminExpired = ctxNone.withAuthorizationHeader(Header(operator).expired)
        val ctxAdminValid = ctxNone.withAuthorizationHeader(Header(operator).expiresTomorrow)

        def call(ctx: LedgerContext) =
          ctx.packageManagementService.uploadDarFile(
            new UploadDarFileRequest(ByteString.copyFrom(darFile)))

        for {
          _ <- mustBeDenied(call(ctxNone)) // Uploading packages without authorization
          _ <- mustBeDenied(call(ctxAlice)) // Uploading packages as Alice (a regular user)
          _ <- call(ctxAdmin) // Uploading packages as Operator (an admin)
          _ <- mustBeDenied(call(ctxAdminExpired))
          _ <- call(ctxAdminValid)
        } yield {
          succeed
        }
      }
    }
  }

  "PartyManagementService" when {
    "listKnownParties" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAdmin = ctxNone.withAuthorizationHeader(Header(operator))
        val ctxAdminExpired = ctxNone.withAuthorizationHeader(Header(operator).expired)
        val ctxAdminValid = ctxNone.withAuthorizationHeader(Header(operator).expiresTomorrow)

        def call(ctx: LedgerContext) =
          ctx.partyManagementService.listKnownParties(new ListKnownPartiesRequest())

        for {
          _ <- mustBeDenied(call(ctxNone)) // Listing known parties without authorization
          _ <- mustBeDenied(call(ctxAlice)) // Listing known parties as Alice (a regular user)
          _ <- call(ctxAdmin) // Listing known parties as Operator (an admin)
          _ <- mustBeDenied(call(ctxAdminExpired))
          _ <- call(ctxAdminValid)
        } yield {
          succeed
        }
      }
    }
    "allocateParty" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAdmin = ctxNone.withAuthorizationHeader(Header(operator))
        val ctxAdminExpired = ctxNone.withAuthorizationHeader(Header(operator).expired)
        val ctxAdminValid = ctxNone.withAuthorizationHeader(Header(operator).expiresTomorrow)

        def call(ctx: LedgerContext) =
          ctx.partyManagementService.allocateParty(
            new AllocatePartyRequest(UUID.randomUUID.toString))

        for {
          _ <- mustBeDenied(call(ctxNone)) // Allocating a party without authorization
          _ <- mustBeDenied(call(ctxAlice)) // Allocating a party as Alice (a regular user)
          _ <- call(ctxAdmin) // Allocating a party as Operator (an admin)
          _ <- mustBeDenied(call(ctxAdminExpired))
          _ <- call(ctxAdminValid)
        } yield {
          succeed
        }
      }
    }
  }

  "TimeService" when {
    "getTime" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId.unwrap
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxAdmin = ctxNone.withAuthorizationHeader(Header(operator))
        val ctxAdminExpired = ctxNone.withAuthorizationHeader(Header(operator).expired)
        val ctxAdminValid = ctxNone.withAuthorizationHeader(Header(operator).expiresTomorrow)

        def call(ctx: LedgerContext) =
          streamResult[GetTimeResponse](observer =>
            ctx.timeService.getTime(new GetTimeRequest(ledgerId), observer))

        for {
          _ <- mustBeDenied(call(ctxNone)) // Getting the time without authorization
          _ <- call(ctxAlice) // Getting the time as Alice (a regular user)
          _ <- call(ctxAdmin) // Getting the time as Operator (an admin)
          _ <- mustBeDenied(call(ctxAliceExpired))
          _ <- call(ctxAliceValid)
          _ <- mustBeDenied(call(ctxAdminExpired))
          _ <- call(ctxAdminValid)
        } yield {
          succeed
        }
      }
    }
  }

  "TransactionService" when {
    "getLedgerEnd" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId.unwrap
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxAdmin = ctxNone.withAuthorizationHeader(Header(operator))
        val ctxAdminExpired = ctxNone.withAuthorizationHeader(Header(operator).expired)
        val ctxAdminValid = ctxNone.withAuthorizationHeader(Header(operator).expiresTomorrow)
        def call(ctx: LedgerContext) =
          ctx.transactionService.getLedgerEnd(new GetLedgerEndRequest(ledgerId))

        for {
          _ <- mustBeDenied(call(ctxNone)) // Reading ledger end without authorization
          _ <- call(ctxAlice) // Reading ledger end as Alice (a regular user)
          _ <- call(ctxAdmin) // Reading ledger end as Operator (an admin)
          _ <- mustBeDenied(call(ctxAliceExpired))
          _ <- call(ctxAliceValid)
          _ <- mustBeDenied(call(ctxAdminExpired))
          _ <- call(ctxAdminValid)
        } yield {
          succeed
        }
      }
    }
    "getTransactions" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId.unwrap
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxBob = ctxNone.withAuthorizationHeader(Header(bob))
        def call(ctx: LedgerContext, party: String) =
          streamResult[GetTransactionsResponse](
            observer =>
              ctx.transactionService.getTransactions(
                new GetTransactionsRequest(ledgerId, Some(ledgerBegin), None, txFilterFor(party)),
                observer))

        for {
          _ <- mustBeDenied(call(ctxNone, alice)) // Reading transactions for Alice without authorization
          _ <- mustBeDenied(call(ctxBob, alice)) // Reading transactions for Alice as Bob
          _ <- call(ctxAlice, alice) // Reading transactions for Alice as Alice
          _ <- mustBeDenied(call(ctxAliceExpired, alice))
          _ <- call(ctxAliceValid, alice)
        } yield {
          succeed
        }
      }
    }
    "getTransactionTrees" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId.unwrap
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxBob = ctxNone.withAuthorizationHeader(Header(bob))
        def call(ctx: LedgerContext, party: String) =
          streamResult[GetTransactionTreesResponse](
            observer =>
              ctx.transactionService.getTransactionTrees(
                new GetTransactionsRequest(ledgerId, Some(ledgerBegin), None, txFilterFor(party)),
                observer))

        for {
          _ <- mustBeDenied(call(ctxNone, alice)) // Reading transactions for Alice without authorization
          _ <- mustBeDenied(call(ctxBob, alice)) // Reading transactions for Alice as Bob
          _ <- call(ctxAlice, alice) // Reading transactions for Alice as Alice
          _ <- mustBeDenied(call(ctxAliceExpired, alice))
          _ <- call(ctxAliceValid, alice)
        } yield {
          succeed
        }
      }
    }
    "getTransactionById" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId.unwrap
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxBob = ctxNone.withAuthorizationHeader(Header(bob))
        def call(ctx: LedgerContext, party: String) =
          ctx.transactionService.getTransactionById(
            new GetTransactionByIdRequest(ledgerId, "does-not-exist", List(party)))
        for {
          _ <- mustBeDenied(call(ctxNone, alice)) // Reading transactions for Alice without authorization
          _ <- mustBeDenied(call(ctxBob, alice)) // Reading transactions for Alice as Bob
          _ <- mustFailWith(call(ctxAlice, alice), Status.Code.NOT_FOUND) // Reading transactions for Alice as Alice
          _ <- mustBeDenied(call(ctxAliceExpired, alice))
          _ <- mustFailWith(call(ctxAliceValid, alice), Status.Code.NOT_FOUND)
        } yield {
          succeed
        }
      }
    }
    "getTransactionByEventId" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId.unwrap
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxBob = ctxNone.withAuthorizationHeader(Header(bob))
        def call(ctx: LedgerContext, party: String) =
          ctx.transactionService.getTransactionByEventId(
            new GetTransactionByEventIdRequest(ledgerId, "does-not-exist", List(party)))

        for {
          _ <- mustBeDenied(call(ctxNone, alice)) // Reading transactions for Alice without authorization
          _ <- mustBeDenied(call(ctxBob, alice)) // Reading transactions for Alice as Bob
          _ <- mustFailWith(call(ctxAlice, alice), Status.Code.NOT_FOUND) // Reading transactions for Alice as Alice
          _ <- mustBeDenied(call(ctxAliceExpired, alice))
          _ <- mustFailWith(call(ctxAliceValid, alice), Status.Code.NOT_FOUND)
        } yield {
          succeed
        }
      }
    }
    "getFlatTransactionById" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId.unwrap
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxBob = ctxNone.withAuthorizationHeader(Header(bob))
        def call(ctx: LedgerContext, party: String) =
          ctx.transactionService.getFlatTransactionById(
            new GetTransactionByIdRequest(ledgerId, "does-not-exist", List(party)))

        for {
          _ <- mustBeDenied(call(ctxNone, alice)) // Reading transactions for Alice without authorization
          _ <- mustBeDenied(call(ctxBob, alice)) // Reading transactions for Alice as Bob
          _ <- mustFailWith(call(ctxAlice, alice), Status.Code.NOT_FOUND) // Reading transactions for Alice as Alice
          _ <- mustBeDenied(call(ctxAliceExpired, alice))
          _ <- mustFailWith(call(ctxAliceValid, alice), Status.Code.NOT_FOUND)
        } yield {
          succeed
        }
      }
    }
    "getFlatTransactionByEventId" should {
      "work only when authorized" in allFixtures { ctxNone =>
        val ledgerId = ctxNone.ledgerId.unwrap
        val ctxAlice = ctxNone.withAuthorizationHeader(Header(alice))
        val ctxAliceExpired = ctxNone.withAuthorizationHeader(Header(alice).expired)
        val ctxAliceValid = ctxNone.withAuthorizationHeader(Header(alice).expiresTomorrow)
        val ctxBob = ctxNone.withAuthorizationHeader(Header(bob))
        def call(ctx: LedgerContext, party: String) =
          ctx.transactionService.getFlatTransactionByEventId(
            new GetTransactionByEventIdRequest(ledgerId, "does-not-exist", List(party)))

        for {
          _ <- mustBeDenied(call(ctxNone, alice)) // Reading transactions for Alice without authorization
          _ <- mustBeDenied(call(ctxBob, alice)) // Reading transactions for Alice as Bob
          _ <- mustFailWith(call(ctxAlice, alice), Status.Code.NOT_FOUND) // Reading transactions for Alice as Alice
          _ <- mustBeDenied(call(ctxAliceExpired, alice))
          _ <- mustFailWith(call(ctxAliceValid, alice), Status.Code.NOT_FOUND)
        } yield {
          succeed
        }
      }
    }
  }

  private def mustBeDenied[T](future: Future[T]): Future[Throwable] =
    mustFailWith(future, Status.Code.PERMISSION_DENIED)

  private def mustFailWith[T](future: Future[T], expectedCode: Status.Code): Future[Throwable] = {
    future.failed.flatMap({
      case sre: StatusRuntimeException if sre.getStatus.getCode == expectedCode =>
        Future.successful(sre)
      case se: StatusException if se.getStatus.getCode == expectedCode => Future.successful(se)
      case t: Throwable =>
        Future.failed(new RuntimeException(s"Expected error $expectedCode, got $t"))
    })
  }

  private def txFilterFor(party: String) = Some(TransactionFilter(Map(party -> Filters())))

  private def ledgerBegin =
    LedgerOffset(LedgerOffset.Value.Boundary(LedgerOffset.LedgerBoundary.LEDGER_BEGIN))

  /** Returns a future that fails iff the given stream immediately fails. */
  private def streamResult[T](fn: StreamObserver[T] => Unit): Future[Unit] = {
    val promise = Promise[Unit]()
    fn(new StreamObserver[T] {
      def onNext(value: T): Unit = {
        val _ = promise.trySuccess(())
      }
      def onError(t: Throwable): Unit = {
        val _ = promise.tryFailure(t)
      }
      def onCompleted(): Unit = {
        val _ = promise.trySuccess(())
      }
    })
    promise.future
  }

  private def expectExpiration[T](fn: StreamObserver[T] => Unit): Future[Unit] = {
    val promise = Promise[Unit]()
    fn(new StreamObserver[T] {
      @volatile private[this] var gotSomething = false
      def onNext(value: T): Unit = {
        gotSomething = true
      }
      def onError(t: Throwable): Unit = {
        t match {
          case e: StatusException
              if e.getStatus.getCode == Status.Code.PERMISSION_DENIED && gotSomething =>
            val _ = promise.trySuccess(())
          case e: StatusRuntimeException
              if e.getStatus.getCode == Status.Code.PERMISSION_DENIED && gotSomething =>
            val _ = promise.trySuccess(())
          case _ =>
            val _ = promise.tryFailure(t)
        }
      }
      def onCompleted(): Unit = {
        val _ = promise.tryFailure(new RuntimeException("stream completed before token expiration"))
      }
    })
    promise.future
  }

  private def dummyCommandRequest(ledgerId: LedgerId, submitter: String) =
    testCommands
      .dummyCommands(ledgerId, s"AuthorizationIT-${UUID.randomUUID}", submitter)
      .update(_.commands.applicationId := testApplicationId)

  private def dummySubmitAndWaitRequest(ledgerId: LedgerId, submitter: String) =
    SubmitAndWaitRequest(dummyCommandRequest(ledgerId, submitter).commands)

}
