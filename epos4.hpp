#include "mbed.h"

namespace epos4 {

  enum epos4State : uint8_t {
    NotReadyToSwitchOn  = 0,
    SwitchOnDisabled    = 1,
    ReadyToSwitchOn     = 2,
    SwitchedOn          = 3,

    OperationEnabled    = 4,
    QuickStopActive     = 5,

    FaultReactionActive = 6,
    Fault               = 7,

    Unknown             = 255,
  };

  extern void init (PinName rx, PinName tx);
  extern void start ();
  extern void stop ();
}
