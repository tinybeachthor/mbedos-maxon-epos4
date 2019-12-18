#include "epos4.hpp"

#include "nmt_messages.hpp"
#include "epos4_messages.hpp"

#include "debug.hpp"

CANMessage constructCANMessage (const uint8_t* raw, const uint8_t NODE_ID) {
  CANMessage out;
  out.format = CANStandard; // Standard format - 11bits
  out.id = 0x600 + NODE_ID; // Function code (RCV SDO) + NODE_ID
  memcpy(out.data, raw, 8);
  out.len = 8;

  return out;
}

Epos4::epos_state Epos4::pollState () {

  // TODO : transition to states

  // TODO : sync state reading + block for update here

  CANMessage out;
  out.format = CANStandard; // Standard format - 11bits
  out.id = 0x600 + NODE_ID; // Function code (RCV SDO) + NODE_ID
  memcpy(out.data, &epos4_messages::Statusword_Data, 4);
  out.len = 4;
  can::put(out);

  CANMessage in;
  can::get(in, osWaitForever);

  uint16_t data;
  memcpy(&data, in.data, in.len);
  return statuswordToState(data);
}

void Epos4::blockForState (Epos4::epos_state desired) {
  pc.printf("Waiting for state : %d\n", desired);
  epos_state state = Unknown;
  do {
    state = pollState();
    pc.printf("Received state : %d\n", state);
  }
  while (state != desired);

  pc.printf("State attained : %d\n", desired);
}

Epos4::Epos4 (PinName rx, PinName tx)
  : nmt_current_state(NMT_Unknown)
{
  nmt_cond = new ConditionVariable(nmt_access);

  can::init(rx, tx, 500000);
  can_listener.start(callback(this, &Epos4::can_handler_routine));

  // Wait for first HEARTBEAT message to arrive
  block_for_nmt_state(nmt_state::PreOperational);
  pc.printf("Got to NMT PreOperational\n");

  // Go to NMT Operational
  can::put(nmt_messages::construct(nmt_messages::Operational));
  block_for_nmt_state(nmt_state::Operational);
  pc.printf("Got to NMT Operational\n");
}

void Epos4::startPosMode () {
  blockForState(SwitchOnDisabled);

  // Shutdown (-> ReadyToSwitchOn)
  can::put(epos4_messages::constructControlword(epos4_messages::Shutdown, NODE_ID));
  ThisThread::sleep_for(50);
  blockForState(ReadyToSwitchOn);

  // Set profile position mode (PPM)
  can::put(constructCANMessage(epos4_messages::SetPPM_Data, NODE_ID));
  ThisThread::sleep_for(50);

  // TODO ? Setup units

  // TODO ? Setup PDOs

  // Switch on  (-> SwitchedOn), allow high voltage
  can::put(epos4_messages::constructControlword(epos4_messages::SwitchOn, NODE_ID));
  ThisThread::sleep_for(50);
  blockForState(SwitchedOn);
  // Enable operation (-> OperationEnabled), allow torque
  can::put(epos4_messages::constructControlword(epos4_messages::EnableOperation, NODE_ID));
  ThisThread::sleep_for(50);
  blockForState(OperationEnabled);
}

void Epos4::stop () {
  // TODO stop
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
