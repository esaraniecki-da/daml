// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.http.dbbackend

import doobie._
import doobie.implicits._
import scalaz.{@@, Tag}
import scalaz.syntax.std.option._
import spray.json._
import cats.syntax.applicative._
import cats.syntax.apply._
import cats.syntax.functor._

object Queries {
  import Implicits._

  def dropTableIfExists(table: String): Fragment = Fragment.const(s"DROP TABLE IF EXISTS ${table}")

  // NB: #, order of arguments must match createContractsTable
  final case class DBContract[+TpId, +CA, +WP](
      contractId: String,
      templateId: TpId,
      createArguments: CA,
      witnessParties: WP)

  val createContractsTable: Fragment = sql"""
      CREATE TABLE
        contract
        (contract_id TEXT PRIMARY KEY NOT NULL
        ,tpid BIGINT NOT NULL REFERENCES template_id (tpid)
        ,create_arguments JSONB NOT NULL
        ,witness_parties JSONB NOT NULL
        )
    """

  val indexContractsTable: Fragment = sql"""
      CREATE INDEX ON contract (tpid)
    """

  final case class DBOffset[+TpId](party: String, templateId: TpId, lastOffset: String)

  val createOffsetTable: Fragment = sql"""
      CREATE TABLE
        ledger_offset
        (party TEXT NOT NULL
        ,tpid BIGINT NOT NULL REFERENCES template_id (tpid)
        ,last_offset TEXT NOT NULL
        ,PRIMARY KEY (party, tpid)
        )
    """

  sealed trait SurrogateTpIdTag
  val SurrogateTpId = Tag.of[SurrogateTpIdTag]
  type SurrogateTpId = Long @@ SurrogateTpIdTag // matches tpid (BIGINT) below

  val createTemplateIdsTable: Fragment = sql"""
      CREATE TABLE
        template_id
        (tpid BIGSERIAL PRIMARY KEY NOT NULL
        ,package_id TEXT NOT NULL
        ,template_module_name TEXT NOT NULL
        ,template_entity_name TEXT NOT NULL
        ,UNIQUE (package_id, template_module_name, template_entity_name)
        )
    """

  private[http] def initDatabase(implicit log: LogHandler): ConnectionIO[Unit] =
    (createTemplateIdsTable.update.run
      *> createOffsetTable.update.run
      *> createContractsTable.update.run
      *> indexContractsTable.update.run).void

  def surrogateTemplateId(packageId: String, moduleName: String, entityName: String)(
      implicit log: LogHandler): ConnectionIO[SurrogateTpId] =
    sql"""SELECT tpid FROM template_id
          WHERE (package_id = $packageId AND template_module_name = $moduleName
                 AND template_entity_name = $entityName)"""
      .query[SurrogateTpId]
      .option flatMap {
      _.cata(
        _.pure[ConnectionIO],
        sql"""INSERT INTO template_id (package_id, template_module_name, entity_name)
              VALUES ($packageId, $moduleName, $entityName)""".update
          .withUniqueGeneratedKeys[SurrogateTpId]("tpid")
      )
    }

  def lastOffset(party: String, tpid: SurrogateTpId)(
      implicit log: LogHandler): ConnectionIO[Option[String]] =
    sql"""SELECT last_offset FROM ledger_offset WHERE (party = $party AND tpid = $tpid)"""
      .query[String]
      .option

  private[http] def updateOffset(party: String, tpid: SurrogateTpId, newOffset: String)(
      implicit log: LogHandler): ConnectionIO[Unit] =
    sql"""INSERT INTO last_offset VALUES ($party, $tpid, $newOffset)
          ON CONFLICT (party, tpid) DO UPDATE (last_offset = $newOffset)""".update.run.void

  def insertContract[CA: JsonWriter, WP: JsonWriter](
      dbc: DBContract[SurrogateTpId, CA, WP]): Fragment =
    Update[DBContract[SurrogateTpId, JsValue, JsValue]]("""
        INSERT INTO contract
        VALUES (?, ?, ?::jsonb, ?::jsonb)
      """).toFragment(
      dbc.copy(
        createArguments = dbc.createArguments.toJson,
        witnessParties = dbc.witnessParties.toJson))

  object Implicits {
    implicit val `JsValue put`: Put[JsValue] =
      Put[String].tcontramap(_.compactPrint)

    implicit val `SurrogateTpId meta`: Meta[SurrogateTpId] =
      SurrogateTpId subst Meta[Long]
  }
}
