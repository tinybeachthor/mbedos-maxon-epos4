#include "epos4.hpp"

#include "can.hpp"
#include "epos4_messages.hpp"

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

namespace epos4 {

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
    CANMessage out;
    out.format = CANStandard; // Standard format - 11bits
    out.id = 0x600 + 0;       // Function code + NODE_ID (0 = broadcast)
    memcpy(out.data, &epos4_messages::StatuswordData, 4);
    out.len = 4;
    can::put(out);

    CANMessage in;
    can::get(in, osWaitForever);

    uint16_t data;
    memcpy(&data, in.data, in.len);
    return statuswordToState(data);
  }

  void blockForState (epos4State desired) {
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

    // NMT -> Operational ? : TODO
  }

  void startPosMode () {
    blockForState(SwitchOnDisabled);
    can::put(epos4_messages::constructControlword(
          epos4_messages::SwitchOnAndEnableOperation));

/* const char SwitchOnDisabled_Data[8] = {0x2B,0x40,0x60,0x00,0x00,0x00,0x00,0x00}; */
/* const char ReadyForSwitchOn_Data[8] = {0x2B,0x40,0x60,0x00,0x06,0x00,0x00,0x00}; */
/* const char SwitchOn_Data[8] = {0x2B,0x40,0x60,0x00,0x07,0x00,0x00,0x00}; */
/* const char OperationEnable_Data[8] = {0x2B,0x40,0x60,0x00,0x0F,0x00,0x00,0x00}; */
/* const char ReSet1_Data[8] = {0x2B,0x40,0x60,0x00,0x00,0x00,0x00,0x00}; */
/* const char ReSet2_Data[8] = {0x2B,0x40,0x60,0x00,0x80,0x00,0x00,0x00}; */
/* const char StatusWord_Data[4] = {0x40,0x41,0x60,0x00}; */
/* const char Pos_Mode_Data[8] = {0x2F,0x60,0x60,0x00,0xFF,0x00,0x00,0x00}; */
/* const char Req_Current_Pos_Data[4] = {0x40,0x64,0x60,0x00}; */
/* const char Homing_Mode_Data[8] = {0x2F,0x60,0x60,0x00,0x06,0x00,0x00,0x00}; */
/* const char Homing_Method_Data_positive[8] = {0x2F,0x98,0x60,0x00,0xFD,0x00,0x00,0x00}; */
/* const char Homing_Method_Data_negative[8] = {0x2F,0x98,0x60,0x00,0xFC,0x00,0x00,0x00}; */
/* const char StartHoming_Data[8] = {0x2B,0x40,0x60,0x00,0x1F,0x00,0x00,0x00}; */
/* const char Homing_Method_current_pos_Data[8] = {0x2F,0x60,0x60,0x00,0x23,0x00,0x00,0x00}; */

    /* //SwitchOnDisabled */
    /* int foo=0; */
    /* foo += can.write(SwitchOnDisabled()); */
    /* Thread::wait(50); */

    /* //ReSet */
    /* foo += can.write(ReSet1()); */
    /* Thread::wait(50); */

    /* //ReSet */
    /* foo += can.write(ReSet2()); */
    /* Thread::wait(50); */

    /* //ReadyForSwitchOn */
    /* foo += can.write(ReadyForSwitchOn()); */
    /* Thread::wait(50); */

    /* //Pos_Mode */
    /* foo += can.write(Pos_Mode()); */
    /* Thread::wait(50); */

    /* //SwitchOn */
    /* foo += can.write(SwitchOn()); */
    /* Thread::wait(50); */

    /* //OperationEnable */
    /* foo += can.write(OperationEnable()); */
    /* Thread::wait(50); */

    // Setup units ?
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
