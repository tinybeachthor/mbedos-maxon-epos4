#pragma once

#include "mbed.h"
#include <stdint.h>

/*
Profile Position Modular (PPM)

Inputs:
  Profile velocity        0x6081
  Max profile velocity    0x607F
  Target position         0x607A
  Software position limit 0x607D

  Controlword             0x6040

  Profile acceleration    0x6083
  Profile deceleration    0x6084
  Quick stop deceleration 0x6085

  Motion profile type     0x6086

Outputs:
  Statusword              0x6041

  EMCY objects for Emergency Telegrams
*/

/* const char ReadyForSwitchOn_Data[8] = {0x2B,0x40,0x60,0x00,0x06,0x00,0x00,0x00}; */
/* const char SwitchOn_Data[8] = {0x2B,0x40,0x60,0x00,0x07,0x00,0x00,0x00}; */

/* const char ReSet1_Data[8] = {0x2B,0x40,0x60,0x00,0x00,0x00,0x00,0x00}; */
/* const char ReSet2_Data[8] = {0x2B,0x40,0x60,0x00,0x80,0x00,0x00,0x00}; */
/* const char Pos_Mode_Data[8] = {0x2F,0x60,0x60,0x00,0xFF,0x00,0x00,0x00}; */
/* const char Req_Current_Pos_Data[4] = {0x40,0x64,0x60,0x00}; */

namespace epos4_messages {

  // Message format:
  // 0          1       2      3          4-7
  // Specifier  Index   Index  Subindex   Data

  const uint8_t StatuswordData[4]  = {0x40,0x41,0x60,0x00};

  const uint8_t ControlwordHeader[8] = {0x2B,0x40,0x60,0x00,0x00,0x00,0x00,0x00};
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
    msg.id = 0x600 + 0;       // Function code + NODE_ID (0 = broadcast)
    memcpy(msg.data, &ControlwordHeader, 8);

    memcpy(msg.data + 4, &cw, 1);

    msg.len = 8;

    return msg;
  }

  enum PPM_Parameters : uint16_t {

    // Configuration
    SOFTWARE_POSITION_LIMIT = 0x607D, // ARRAY - 1-2 subindex
      // subindex 1 - INTEGER32 Min Position Limit
      // subindex 2 - INTEGER32 Max Position Limit

    MAX_PROFILE_VELOCITY    = 0x607F, // UNSIGNED32
    MAX_MOTOR_SPEED         = 0x6080, // UNSIGNED32

    MAX_GEAR_INPUT_SPEED    = 0x3003, // RECORD - 1-4 subindex
      // subindex 1 - UNSIGNED32 Gear reduction numerator
      // subindex 2 - UNSIGNED32 Gear reduction denominator
      // subindex 3 - UNSIGNED32 Max gear input speed
      // subindex 4 - UNSIGNED32 Gear miscellaneous configuration
        // bits 31..1 - reserved
        // bit 0 - Gear direction = 0 - Normal; 1 - Inverted;

    QUICK_STOP_DECELERATION = 0x6085, // UNSIGNED32
    MAX_ACCELERATION        = 0x60C5, // UNSIGNED32

    // Commanding
    CONTROLWORD             = 0x6040, // UNSIGNED16
      // Supervision of operating modes
      // Bit
      // 15     Endless movement (in PPM), Reserved in other modes
      // 14..9  Reserved
      // 8      Halt (in PPM, PVM, HMM)
      // 7      Fault Reset
      // 6      Abs / rel (in PPM), Reserved in other modes
      // 5      Change set immediately (in PPM), Reserved in other modes
      // 4      New setpoint (in PPM), Homin operating start (in HMM)
      // 3      Enable operation
      // 2      Quick stop
      // 1      Enable voltage
      // 0      Switched on

    TARGET_POSITION         = 0x607A, // INTEGER32
    PROFILE_VELOCITY        = 0x6081, // UNSIGNED32
    PROFILE_ACCELERATION    = 0x6083, // UNSIGNED32
    PROFILE_DECCELERATION   = 0x6084, // UNSIGNED32

    MOTION_PROFILE_TYPE     = 0x6086, // INTEGER16
      // 0 - linear ramp (trapezoidal profile)
  };

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
