// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.extractor

import java.io.File

import com.digitalasset.daml.bazeltools.BazelRunfiles.rlocation
import com.digitalasset.extractor.services.{CustomMatchers, ExtractorFixtureAroundAll}
import com.digitalasset.ledger.api.testing.utils.SuiteResourceManagementAroundAll
import com.digitalasset.platform.sandbox.persistence.PostgresAroundAll
import io.circe.parser._
import org.scalatest.{FlatSpec, Inside, Matchers, Suite}
import scalaz.Scalaz._

class EnumSpec
    extends FlatSpec
    with Suite
    with PostgresAroundAll
    with SuiteResourceManagementAroundAll
    with ExtractorFixtureAroundAll
    with Inside
    with Matchers
    with CustomMatchers {

  override protected def darFile = new File(rlocation("daml-lf/encoder/test-1.6.dar"))

  override def scenario: Option[String] = Some("EnumMod:createContracts")

  "Enum" should "be extracted" in {
    getContracts should have length 3
  }

  it should "contain the correct JSON data" in {

    val contractsJson = getContracts.map(_.create_arguments)

    val expected = List(
      """{
      "x" : "Red",
      "party" : "Bob"
      }""",
      """{
      "x" : "Green",
      "party" : "Bob"
      }""",
      """{
      "x" : "Blue",
      "party" : "Bob"
      }"""
    ).traverseU(parse)

    expected should be('right) // That should only fail if this JSON^^ is ill-formatted

    contractsJson should contain theSameElementsAs expected.right.get
  }

}
