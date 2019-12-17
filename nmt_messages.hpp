#pragma once

#include "mbed.h"
#include <stdint.h>

namespace nmt_messages {

  /* NMT objects

  Function code + NODE_ID = 0x000

  Identifier 0, 2 bytes
    | 0    | 1         | Byte#
    | CS   | Node-ID   | Name
    | ---  | ---       |
    | 0x80 | 0 (all)   | All CANOpen will enter Pre-Operational
    | 0x82 | 0         | Reset Communication
    | 0x81 | 0         | Reset Node
    | 0x01 | 0         | Start - Enter Operational
    | 0x02 | 0         | Stop  - Enter Stopped

  Node-ID - 0 for all, n for ID

  */

  enum transition : uint8_t {
    PreOperational     = 0x80,

    ResetCommunication = 0x82,
    ResetNode          = 0x83,

    Operational        = 0x01,
    Stopped            = 0x02,
  };

  inline CANMessage construct (transition t) {
    const uint8_t nmt_Template[8] = {0x00,0x00,0x00,0x00,0x00,0x00,0x00,0x00};

    CANMessage msg;

    msg.format = CANStandard; // Standard format - 11bits
    msg.id = 0x000;
    memcpy(msg.data, &nmt_Template, 8);

    memcpy(msg.data, &t, 1);

    msg.len = 8;

    return msg;
  }
}
