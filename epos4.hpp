#include "mbed.h"

class Epos4 {

public:
  Epos4 (PinName rx, PinName tx);

  void startPosMode ();
  void stop ();

private:
};
