#include "epos4.hpp"

#include "can.hpp"
#include "epos4_messages.hpp"

namespace epos4 {

  // TODO : make this a class

  CANMessage constructCANMessage (const uint8_t* raw) {
    CANMessage out;
    out.format = CANStandard; // Standard format - 11bits
    out.id = 0x600 + 0;       // Function code (RCV SDO) + NODE_ID
    memcpy(out.data, raw, 8);
    out.len = 8;

    return out;
  }

  epos4State statuswordToState(uint16_t statusword) {
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

  epos4State pollState () {

    // TODO : thread listen for messages + transition to states
    // TODO : sync state reading + block for update here

    CANMessage out;
    out.format = CANStandard; // Standard format - 11bits
    out.id = 0x600 + 0;       // Function code (RCV SDO) + NODE_ID
    memcpy(out.data, &epos4_messages::Statusword_Data, 4);
    out.len = 4;
    can::put(out);

    CANMessage in;
    can::get(in, osWaitForever);

    uint16_t data;
    memcpy(&data, in.data, in.len);
    return statuswordToState(data);
  }

  void blockForState (epos4State desired) {
    pc.printf("Waiting for state : %d", desired);
    epos4State state = Unknown;
    do {
      state = pollState();
      pc.printf("Received state : %d", state);
    }
    while (state != desired);

    pc.printf("State attained : %d", desired);
  }

  void init (PinName rx, PinName tx) {
    can::init(rx, tx, 500000);

    // TODO : listen for heartbeat -> get NODE_ID

    // NMT -> Operational TODO
  }

  void startPosMode () {
    blockForState(SwitchOnDisabled);

    // Shutdown (-> ReadyToSwitchOn)
    can::put(epos4_messages::constructControlword(epos4_messages::Shutdown));
    Thread::wait(50);
    blockForState(ReadyToSwitchOn);

    // Set profile position mode (PPM)
    can::put(constructCANMessage(&SetPPM_Data));
    Thread::wait(50);

    // Setup units ? TODO

    // Setup PDOs ? TODO

    // Switch on  (-> SwitchedOn), allow high voltage
    can::put(epos4_messages::constructControlword(epos4_messages::SwitchedOn));
    Thread::wait(50);
    blockForState(SwitchedOn);
    // Enable operation (-> OperationEnabled), allow torque
    can::put(epos4_messages::constructControlword(epos4_messages::EnableOperation));
    Thread::wait(50);
    blockForState(OperationEnabled);
  }

  /* void quickStop () { */
  /*   // Send <<Quickstop>> controlword */
  /*   // Wait for QuickStopActive */
  /* } */
  /* void resume() { */
  /*   // Send <<EnableOperation>> */
  /*   // Wait for OperationEnabled */
  /* } */

  /* void resetError() { */
  /*   // Send <<Fault reset>> controlword */
  /*   // Wait for SwitchOnDisabled */
  /* } */

  /* namespace NMT { */

    /*
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

  /*   enum State { */
  /*     Initialization, */
  /*     PreOperational, */
  /*     Operational, */
  /*     Stopped, */
  /*   }; */

  /*   bool goToState (State nextState); */
  /*   bool resetCommunication (); */
  /* } */

  /* namespace EMCY { */
  /*   getError( data ) { */
  /*     // byte 0,1 = ErrorCode */
  /*     // byte 2 = Error Register */
  /*   } */

  /*   resettableError ( errorCode ) { */
  /*     // not resettables: */

  /*     //  0x1080 ... 0x1083 - Generic Initialization error - reset device, if persist contact supplier */
  /*     //  0x1090 - Firmware incompatibility error - reset / update firmware / contact supplier */
  /*     //  0x3210 - Overvoltage error - Usually at deceleration (consult Firmware Specification for hardware solution, add capacitor), CAN TRY RESET - if voltage valid */
  /*     //  0x4210 - Thermal overload error - CAN TRY RESET - if temperature in valid range */
  /*     //  0x4380 - Thermal motor overload error - CAN TRY RESET if corrected */
  /*     //  0x5113 - Logic voltage too low - CAN TRY RESET if corrected */

  /*     //  0x5280 - reset device */
  /*     //  0x5281 - reset device */
  /*     //  0x5480 ... 0x5483 - reset device */
  /*     //  0x6080,0x6081 - can reset + check extension 1 is connected, see manual */
  /*     //  0x6380 - Set device parameters again */

  /*     // 0x8120,0x8130 - send NMT reset communication */

  /*     // 0x8181 - reset device */
  /*   } */
  /* } */
}
