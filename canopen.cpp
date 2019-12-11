#include  "canopen.hpp"

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

/*
Motorcontroller - CANOpen NMT slave

Automatically on boot
Initialization -> Pre-Operational

Pre-operational
  Can be configured using SDO communication.
  Emergency objects.
  NMT Protocol to transition state.
  No PDO communication.

Operational
  SDO, PDO, EMCY, NMT

State transition
  NMT object
    Identifier 0, 2 bytes
      | 0 CS | 1 Node-ID |
      | 0x80 | 0 (all)   | All CANOpen will enter Pre-Operational
      | 0x82 | 0         | Reset Communication
      | 0x81 | 0         | Reset Node
      | 0x01 | 0         | Start - Enter Operational
      | 0x02 | 0         | Stop  - Enter Stopped

    Node-ID - 0 for all, n for ID

*/

namespace CANOpen {
namespace epos4 {

  BufferedCan* bus;

  enum State {
    NotReadyToSwitchOn,
    SwitchOnDisabled,
    ReadyToSwitchOn,
    SwitchedOn,
    OperationEnabled,
    QuickStopActive,
    FaultReactionActive,
    Fault,
    Unknown,
  };
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

  State statuswordToState(uint16_t statusword) {
    uint8_t lowByte = (uint8_t)(statusword & 0xFF);

    lowByte &= 0b01101111; // null 7 and 5 bits

    if (lowByte == 0b00000000)
      return NotReadyToSwitchOn;
    else if (lowByte == 0b01000000)
      return SwitchOnDisabled;
    else if (lowByte == 0b00100001)
      return ReadyToSwitchOn;
    else if (lowByte == 0b00100011)
      return SwitchedOn;
    else if (lowByte == 0b00100111)
      return OperationEnabled;
    else if (lowByte == 0b00000111)
      return QuickStopActive;
    else if (lowByte == 0b00001111)
      return FaultReactionActive;
    else if (lowByte == 0b00001000)
      return Fault;

    return Unknown;
  }

  void initialize ( pins... ) {
    // Setup CAN

    // Wait for SwitchOnDisabled - Statusword
    // Send <<Shutdown>>         - Controlword
    // Wait for ReadyToSwitchOn
    // Send <<SwitchedOn>>
    // Wait for SwitchedOn
    // Send <<EnableOperation>>
    // Wait for OperationEnabled

    // Setup units
  }

  void quickStop () {
    // Send <<Quickstop>> controlword
    // Wait for QuickStopActive
  }
  void resume() {
    // Send <<EnableOperation>>
    // Wait for OperationEnabled
  }

  void resetError() {
    // Send <<Fault reset>> controlword
    // Wait for SwitchOnDisabled
  }

  namespace NMT {
    enum State {
      Initialization,
      PreOperational,
      Operational,
      Stopped,
    };

    bool goToState (State nextState);
    bool resetCommunication ();
  }

  namespace PDO {
  }

  namespace EMCY {
    getError( data ) {
      // byte 0,1 = ErrorCode
      // byte 2 = Error Register
    }

    resettableError ( errorCode ) {
      // not resettables:

      //  0x1080 ... 0x1083 - Generic Initialization error - reset device, if persist contact supplier
      //  0x1090 - Firmware incompatibility error - reset / update firmware / contact supplier
      //  0x3210 - Overvoltage error - Usually at deceleration (consult Firmware Specification for hardware solution, add capacitor), CAN TRY RESET - if voltage valid
      //  0x4210 - Thermal overload error - CAN TRY RESET - if temperature in valid range
      //  0x4380 - Thermal motor overload error - CAN TRY RESET if corrected
      //  0x5113 - Logic voltage too low - CAN TRY RESET if corrected

      //  0x5280 - reset device
      //  0x5281 - reset device
      //  0x5480 ... 0x5483 - reset device
      //  0x6080,0x6081 - can reset + check extension 1 is connected, see manual
      //  0x6380 - Set device parameters again

      // 0x8120,0x8130 - send NMT reset communication

      // 0x8181 - reset device
    }
  }
}
}
