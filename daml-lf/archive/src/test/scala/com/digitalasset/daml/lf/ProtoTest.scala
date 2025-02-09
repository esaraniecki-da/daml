// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.daml.lf

import java.nio.file.{Files, Path, Paths}
import java.util.zip.ZipFile

import com.digitalasset.daml.bazeltools.BazelRunfiles._
import com.digitalasset.{daml_lf_1_6, daml_lf_dev}
import com.google.protobuf.CodedInputStream
import org.scalatest.prop.TableDrivenPropertyChecks
import org.scalatest.{Assertion, Matchers, WordSpec}

import scala.collection.JavaConverters._

class ProtoTest extends WordSpec with Matchers with TableDrivenPropertyChecks {

  private val darFile = resource(rlocation("daml-lf/archive/DarReaderTest.dar"))

  private def resource(path: String): Path = {
    val f = Paths.get(path)
    require(Files.exists(f), s"File does not exist: $f")
    f
  }

  "daml_lf_dev.DamlLf" should {
    "read dalf" in {

      decodeTestWrapper(
        darFile, { cis =>
          val archive = daml_lf_dev.DamlLf.Archive.parseFrom(cis)
          val payload = daml_lf_dev.DamlLf.ArchivePayload.parseFrom(archive.getPayload)
          payload.hasDamlLf1 shouldBe true
        }
      )

    }
  }

  "daml_lf_1_6.DamlLf" should {
    "read dalf" in {
      decodeTestWrapper(
        darFile, { cis =>
          val archive = daml_lf_1_6.DamlLf.Archive.parseFrom(cis)
          val payload = daml_lf_1_6.DamlLf.ArchivePayload.parseFrom(archive.getPayload)
          payload.hasDamlLf1 shouldBe true
        }
      )
    }
  }

  "daml_lf_1_6 file" should {

    // Do not change thiss test.
    // The test checks the snapshot of the proto definition are not modified.

    val rootDir = "daml-lf/archive/src/main/protobuf/com/digitalasset/daml_lf_1_6"

    def resolve(file: String) =
      resource(rlocation(s"$rootDir/$file"))

    "not be modified" in {

      val files = Table(
        ("file", "Linux hash", "windows hash"),
        (
          "daml_lf_0.proto",
          "1554427a861be3fb00a2445711fffe3c54bf0e541be6e748d0a18c5fe01afc03",
          "e79a319ed16dd7cd533d252c2884241759bd9af72f83a4516ff937db53cbcbf8"),
        (
          "daml_lf_1.proto",
          "711b129f810248d20526144d2d56c85fc486b14ba1eb2ab6b13a659a710ad5d2",
          "d75b661509079c12327e18296350aeffb77ca88f8ee110fd1c774ce8c0cb16f0"),
        (
          "daml_lf.proto",
          "4064870ecefaa3b727d67f0b8fa31590c17c7b11ad9ca7c73f2925013edf410e",
          "6b5990fe8ed2de64e3ec56a0d1d0d852983832c805cf1c3f931a0dae5b8e5ae2")
      )

      forEvery(files) {
        case (fileName, linuxHash, windowsHash) =>
          List(linuxHash, windowsHash) should contain(hashFile(resolve(fileName)))
      }
    }
  }

  private def decodeTestWrapper(dar: Path, test: CodedInputStream => Assertion) = {
    val zipFile = new ZipFile(dar.toFile)
    val entries = zipFile.entries().asScala.filter(_.getName.endsWith(".dalf")).toList

    assert(entries.size >= 2)
    assert(entries.exists(_.getName.contains("daml-stdlib")))

    entries.foreach { entry =>
      val inputStream = zipFile.getInputStream(entry)
      try {
        val cos: CodedInputStream = com.google.protobuf.CodedInputStream.newInstance(inputStream)
        test(cos)
      } finally {
        inputStream.close()
      }
    }
  }

  private def hashFile(file: Path) = {
    val bytes = Files.readAllBytes(file)
    java.security.MessageDigest.getInstance("SHA-256").digest(bytes).map("%02x" format _).mkString
  }
}
