// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.daml.ledger.api.testtool.infrastructure

import ai.x.diff._
import com.daml.ledger.api.testtool.infrastructure.LedgerTestSuite.SkipTestException
import com.daml.ledger.api.testtool.infrastructure.participant.ParticipantTestContext
import com.digitalasset.ledger.api.v1.event.{ArchivedEvent, CreatedEvent, Event, ExercisedEvent}
import com.digitalasset.ledger.api.v1.transaction.{Transaction, TransactionTree, TreeEvent}
import com.digitalasset.ledger.test_stable.Test.AgreementFactory
import com.digitalasset.ledger.test_stable.Test.AgreementFactory._
import io.grpc.{Status, StatusException, StatusRuntimeException}
import scalaz.{@@, Tag}

import scala.concurrent.duration.DurationInt
import scala.concurrent.{ExecutionContext, Future}
import scala.language.higherKinds

private[testtool] object LedgerTestSuite {

  final case class SkipTestException(message: String) extends RuntimeException(message)

}

private[testtool] abstract class LedgerTestSuite(val session: LedgerSession) {

  val name: String = getClass.getSimpleName

  val tests: Vector[LedgerTest] = Vector.empty

  protected final implicit val ec: ExecutionContext = session.executionContext

  // TODO Make this configurable
  final private[this] val withRetryStrategy = RetryStrategy.exponentialBackoff(10, 10.millis)

  final def eventually[A](runAssertion: => Future[A]): Future[A] =
    withRetryStrategy { _ =>
      runAssertion
    }

  final def skip(reason: String): Future[Unit] = Future.failed(SkipTestException(reason))

  final def skipIf(reason: String)(p: => Boolean): Future[Unit] =
    if (p) skip(reason) else Future.successful(())

  final def fail(message: => String): Nothing =
    throw new AssertionError(message)

  private def events(tree: TransactionTree): Iterator[TreeEvent] =
    tree.eventsById.valuesIterator

  private def events(transaction: Transaction): Iterator[Event] =
    transaction.events.iterator

  final def archivedEvents(transaction: Transaction): Vector[ArchivedEvent] =
    events(transaction).flatMap(_.event.archived.toList).toVector

  final def createdEvents(tree: TransactionTree): Vector[CreatedEvent] =
    events(tree).flatMap(_.kind.created.toList).toVector

  final def createdEvents(transaction: Transaction): Vector[CreatedEvent] =
    events(transaction).flatMap(_.event.created.toList).toVector

  final def exercisedEvents(tree: TransactionTree): Vector[ExercisedEvent] =
    events(tree).flatMap(_.kind.exercised.toList).toVector

  final def assertLength[A, F[_] <: Seq[_]](context: String, length: Int, as: F[A]): F[A] = {
    assert(as.length == length, s"$context: expected $length item(s), got ${as.length}")
    as
  }

  final def assertSingleton[A](context: String, as: Seq[A]): A =
    assertLength(context, 1, as).head

  final def assertEquals[T: DiffShow](context: String, actual: T, expected: T): Unit = {
    val diff = DiffShow.diff(actual, expected)
    if (!diff.isIdentical)
      throw new AssertionErrorWithPreformattedMessage(
        diff.string,
        s"$context: two objects are supposed to be equal but they are not")
  }

  final def assertGrpcError(t: Throwable, expectedCode: Status.Code, pattern: String): Unit = {

    val (actualCode, message) = t match {
      case sre: StatusRuntimeException => (sre.getStatus.getCode, sre.getStatus.getDescription)
      case se: StatusException => (se.getStatus.getCode, se.getStatus.getDescription)
      case _ =>
        throw new AssertionError(
          "Exception is neither a StatusRuntimeException nor a StatusException")
    }
    assert(actualCode == expectedCode, s"Expected code [$expectedCode], but got [$actualCode].")
    // Note: Status.getDescription() is nullable, map missing descriptions to an empty string
    val nonNullMessage = Option(message).getOrElse("")
    assert(
      nonNullMessage.contains(pattern),
      s"Error message did not contain [$pattern], but was [$nonNullMessage].")
  }

  /**
    * Create a synchronization point between two participants by ensuring that a
    * contract with two distributed stakeholders both see an update on a shared contract.
    *
    * Useful to ensure two parties distributed across participants both view the
    * updates happened _BEFORE_ the call to this method.
    *
    * This allows us to check that an earlier update which is not to be seen on either
    * participant by parties distributed across them is actually not visible and not
    * a byproduct of interleaved distributed calls.
    *
    * FIXME This will _NOT_ work with distributed committers
    */
  final def synchronize(
      alpha: ParticipantTestContext,
      beta: ParticipantTestContext): Future[Unit] = {
    for {
      alice <- alpha.allocateParty()
      bob <- beta.allocateParty()
      factory <- alpha.create(alice, AgreementFactory(bob, alice))
      agreement <- eventually { beta.exercise(bob, factory.exerciseCreateAgreement) }
      _ <- eventually { alpha.transactionTreeById(agreement.transactionId, alice) }
    } yield {
      // Nothing to do, by flatmapping over this we know
      // the two participants are synchronized up to the
      // point before invoking this method
    }
  }

  implicit def diffShowTag[A, T](implicit diffShowA: DiffShow[A]): DiffShow[A @@ T] =
    new DiffShow[A @@ T] {
      override def show(t: A @@ T): String = diffShowA.show(Tag.unwrap(t))

      override def diff(left: A @@ T, right: A @@ T): Comparison =
        diffShowA.diff(Tag.unwrap(left), Tag.unwrap(right))
    }

  implicit def diffShowSeq[T](implicit diffShowT: DiffShow[T]): DiffShow[Seq[T]] =
    new DiffShow[Seq[T]] {
      override def show(t: Seq[T]): String = t.toString

      override def diff(left: Seq[T], right: Seq[T]): Comparison = {
        val changed = left.toStream
          .zip(right.toStream)
          .zipWithIndex
          .map { case ((l, r), index) => index -> diffShowT.diff(l, r) }
          .collect { case (index, diff) if !diff.isIdentical => index.toString -> diff.string }
        val removed = left.toStream.zipWithIndex.drop(right.length).map {
          case (value, index) => index.toString -> red(diffShowT.show(value))
        }
        val added = right.toStream.zipWithIndex.drop(left.length).map {
          case (value, index) => index.toString -> green(diffShowT.show(value))
        }

        assert(
          removed.isEmpty || added.isEmpty,
          "Diff[Seq[_]] thinks that both sequences are longer than each other.")

        if (changed.isEmpty && removed.isEmpty && added.isEmpty) {
          Identical(left)
        } else {
          val changedOption =
            if (changed.isEmpty)
              Stream(None)
            else
              changed.map(Some(_))
          val differences = changedOption ++ removed.map(Some(_)) ++ added.map(Some(_))
          Different(DiffShow.constructorOption("Seq", differences.toList))
        }
      }
    }
}
