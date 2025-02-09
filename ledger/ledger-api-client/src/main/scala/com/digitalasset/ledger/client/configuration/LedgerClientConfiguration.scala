// Copyright (c) 2019 The DAML Authors. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

package com.digitalasset.ledger.client.configuration

import io.netty.handler.ssl.SslContext

/**
  * @param applicationId The string that will be used as an application identifier when issuing commands and retrieving transactions
  * @param ledgerIdRequirement A [[LedgerIdRequirement]] specifying how the ledger identifier must be checked against the one returned by the LedgerIdentityService
  * @param commandClient The [[CommandClientConfiguration]] that defines how the command client should be setup with regards to timeouts, commands in flight and command TTL
  * @param sslContext If defined, the context will be passed on to the underlying gRPC code to ensure the communication channel is secured by TLS
  * @param accessToken If defined, specifies the string representing a token (including the authentication schema) that will be used to access services on a Ledger API server that requires authentication
  */
final case class LedgerClientConfiguration(
    applicationId: String,
    ledgerIdRequirement: LedgerIdRequirement,
    commandClient: CommandClientConfiguration,
    sslContext: Option[SslContext],
    accessToken: Option[String] = None)
