
#include "config.h"

namespace cosa {

APdrConfig GlobalAPdrConfig;

const std::vector<std::string> APdrConfig::function_names = {
      "Function:Idle",
      "Function:SolveTrans",
      "Function:SolveTransLemma",
      "Function:RecursiveBlock",
      "Function:CheckUntil",
      "Function:PushOneFrame",
      "Function:PushEager",
    };

} // namespace cosa

