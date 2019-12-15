#include  "canopen.hpp"

namespace canopen {

  /* void handle_receive(mbed::CANMessage &msg, Process* current_process) { */
  /*   uint64_t data; */

  /*   memcpy(&data, msg.data, msg.len); */

  /*   switch (msg.id) { */
  /*     case CAN_ID_SafeState: { */
  /*       SafeState rcvmsg = unpack<SafeState>(data); */
  /*       channelmanager::notify_listeners<SafeState>(channel::LOOM_SAFESTATE, &rcvmsg, current_process); */
  /*       break; */
  /*     } */
  /*   } */
  /* } */

  /* void transmit(channelmanager::Notifier* notifier) { */
  /*   mbed::CANMessage msg; */

  /*   switch (notifier->channelid) { */
  /*     case channel::LOOM_BUTTONSPRESSED: { */
  /*       ButtonsPressed tosend = notifier->get_data<ButtonsPressed>(); */
  /*       pack<ButtonsPressed>(tosend, (uint64_t&) msg.data[0]); */
  /*       msg.len = ButtonsPressed::_DLC; */
  /*       msg.id = ButtonsPressed::_ID; */
  /*       break; */
  /*     } */
  /*     default: */
  /*       break; */
  /*   } */

  /*   can::write_status ret = bus->write(msg); */
  /*   if(ret == write_status::WRITE_FAIL) { */
  /*     failed_count++; */
  /*     if (failed_count == 100) { */
  /*       failed_count = 0; */
  /*       RTTOUT("100 CAN writes failed, %d sent. \n", sent_count); */
  /*       sent_count = 0; */
  /*       if (sent_count == 0) { */
  /*         bus->reset(); */
  /*       } */
  /*     } */
  /*   } else if (ret == write_status::SEM_FAIL) { */
  /*     RTTOUT("Failed to acquire semaphore\n"); */
  /*   } else { */
  /*     sent_count++; */
  /*   } */
  /* } */

  Process::main loom_transmit_main(Process* current_process) {
    while (Message *message = current_process->receive(true)) {
      if (channelmanager::Notifier* notifier = rtospp::message_cast<channelmanager::Notifier>(message)) {
        transmit(notifier);
        notifier->return_notifier();
      }
    }
  }

  Process::main loom_receive_main(Process* current_process) {
    mbed::CANMessage msg;
    while(true) {
      if (bus->read(msg)) {
        handle_receive(msg, current_process);
      }
    }
  }

}
