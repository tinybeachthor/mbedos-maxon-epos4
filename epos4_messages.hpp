#pragma once

#include "mbed.h"
#include <stdint.h>

/*
Profile Position Modular (PPM)

Settings:
  Max gear input speed    0x3003

Inputs:
  Target position         0x607A

  Profile velocity        0x6081
  Max profile velocity    0x607F
  Software position limit 0x607D
  Max acceleration        0x60C5
  Max motor speed         0x6080

  Controlword             0x6040

  Profile acceleration    0x6083
  Profile deceleration    0x6084
  Quick stop deceleration 0x6085

  Motion profile type     0x6086

Outputs:
  Statusword              0x6041

  EMCY objects for Emergency Telegrams

*/

namespace epos4_messages {
  // Message format:
  // 0          1-2     3          4-7
  // Specifier  Index   Subindex   Data
  //
  // Specifier:
  // | | | |0|n|n|e|s|
  //  0 0 1             - Download (to slave)
  //  0 1 0             - Upload   (from slave)
  //
  // nn - #bytes *not* used in data (bytes 4-6)
  // e  - expedited (full message in single frame)
  // s  - if 1 then data size in nn is to be used

  const uint8_t SetPPM_Data[8] = {0x2F,0x60,0x60,0x00,0xFF,0x00,0x00,0x00};

  const uint8_t Statusword_Data[4]  = {0x40,0x41,0x60,0x00};

  const uint8_t Controlword_Header[8] = {0x2B,0x40,0x60,0x00,0x00,0x00,0x00,0x00};
  enum Controlword : uint16_t {
    Shutdown                   = 0b00000110, // 0xxx x110
    SwitchOn                   = 0b00000111, // 0xxx x111
    SwitchOnAndEnableOperation = 0b00001111, // 0xxx 1111
    DisableVoltage             = 0b00000000, // 0xxx xx0x
    QuickStop                  = 0b00000010, // 0xxx x01x
    DisableOperation           = 0b00000111, // 0xxx 0111
    EnableOperation            = 0b00001111, // 0xxx 1111
    FaultReset                 = 0b11111111, // 0xxx xxxx -> 1xxx xxxx
  };
  inline CANMessage constructControlword(Controlword cw) {
    CANMessage msg;

    msg.format = CANStandard; // Standard format - 11bits
    msg.id = 0x600 + 0;       // Function code (RCV SDO) + NODE_ID
    memcpy(msg.data, &Controlword_Header, 8);

    memcpy(msg.data + 4, &cw, 1);

    msg.len = 8;

    return msg;
  }

  enum ErrorCodes : uint32_t {
    NO_ABORT                          = 0x00000000, // Communication successful
		TOGGLE_ERROR                      = 0x05030000, // Toggle bit not alternated
		SDO_TIMEOUT                       = 0x05040000, // SDO protocol timed out
		COMMAND_UNKNOWN                   = 0x05040001, // Command specifier unknown
		CRC_ERROR                         = 0x05040004, // CRC check failed
		ACCESS_ERROR                      = 0x06010000, // Unsupported access to an object
		WRITE_ONLY_ERROR                  = 0x06010001, // Read command to a write only object
		READ_ONLY_ERROR                   = 0x06010002, // Write command to a read only object
    SUBINDEX_CANNOT_BE_WRITTEN        = 0x06010003, // Subindex cannot be written, subindex must be "0" for write access
		OBJECT_DOES_NOT_EXIST             = 0x06020000, // Last read or write command had wrong object index or subindex
		PDO_MAPPING_ERROR                 = 0x06040041, // Object is not mappable to the PDO
		PDO_LENGTH_ERROR                  = 0x06040042, // Number and length of objects to be mapped would exceed PDO length
		GENERAL_PARAMETER_INCOMPATIBILITY = 0x06040043, // General parameter incompatibility
		GENERAL_INTERNAL_INCOMPATIBILITY  = 0x06040047, // General internal incompatibility in device
		HARDWARE_ERROR                    = 0x06060000, // Access failed due to hardware error
		SERVICE_PARAMETER_ERROR           = 0x06070010, // Data type does not match, length or service parameter do not match
    SERVICE_PARAMETER_TOO_SHORT_ERROR = 0x06070013, // Data types don't match, length of service parameter too long
		SUBINDEX_ERROR                    = 0x06090011, // Last read or write command had wrong object subindex
		VALUE_RANGE                       = 0x06090030, // Value range of parameter exceeded
		GENERAL_ERROR                     = 0x08000000, // General error
		TRANSFER_OR_STORE_ERROR           = 0x08000020, // Data cannot be transferred or stored
		WRONG_DEVICE_STATE                = 0x08000022, // Data cannot be transferred or stored to application because of present device state
		PASSWORD_ERROR                    = 0x0F00FFBE, // Password is incorrect
		ILLEGAL_ERROR                     = 0x0F00FFBF, // Command code is illegal (does not exist)
		FFC0_WRONG_NMT_STATE              = 0x0F00FFC0, // Device is in wrong NMT state
  };
}
