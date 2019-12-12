#pragma once

#include <stdint.h>

/*
  CANOpen implementation for MAXON EPOS4 motor controller

    Only Standard frame format is supported. (11bit COB-IDs)

  OBJECT DICTIONARY
    16bit index + 8bit subindex
    supported index ranges:
    1000h-1FFFh Communication Profile Area (CiA 301)
    2000h-5FFFh Manufacturer-specific Profile Area (maxon motor)
    6000h-9FFFh Standardized Device Area (CiA 402)
    subindex - used to reference ARRAY & RECORD elements
            - 0 for primitive values

  PDO - Process Data Objects - real-time data transfer
  SDO - Service Data Objects - read/write entries of a device Object Dictionary
  SFO - Special Function Objects
    SYNC - Synchronization Objects
    EMCY - Emergency Objects
  NMO - Network Management Objects - Services for network init, error control,
                                     device status control

  PDO
    Non confirmed.
    Producer->Consumer / Broadcast
    TxPDO with a RxPDO identfier of one or more consumers.

    Write PDO - Single CAN Data frame
    Read PDO - CAN Remote Frame, which will be responbed by the corresponding CAN Data frame

    Read PDO - optional
    Number and length of device PDOs are application-specific,
    must be specified in the device profile.

    Number of supported PDOs at the Object Dictionary @ 0x1004h.
    PDO mapping + data types are determined by defaults set at 0x1600h (for the first R_PDO)
    ans 0x1A00h (for the first T_PDO).
    Up to 512 T_PDOs and 512 R_PDOs may be used in a CANOpen network.

  Communication profiles:
    - Event-driven - producer driven
    - Polling by remote frames - consumer driven
    - Synchronized - time driven (polled by SYNC)

  SDO
    Two messages - confirmed communication.
    Can be used to establish a peer-to-peer communication channel.

    One SDO support is mandatory and default.

*/
namespace CANOpen {
namespace epos4 {

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

} // epos4
} // canopen
