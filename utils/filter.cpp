#include "frontends/property_if.h"
#include "filter.h"
#include "core/ts.h"

namespace pono {
AntFilter::AntFilter(const std::string filename, const std::string& filter, TransitionSystem &ts) : filename_(filename),ts_(ts),
   is_reg([this](const std::string & check_name) -> bool{ 
    auto pos = ts_.named_terms().find(check_name);
    if(pos == ts_.named_terms().end())
      return false;
      auto a = ts_.is_curr_var(pos->second);
      auto b = (ts_.state_updates().find(pos->second)!=ts_.state_updates().end());
      return a&&b;
  } )
  
    {
      parse_from(filename, filter, is_reg, true);
    }


bool AntFilter::operator()(const std::string name_check, std::string val_check,const int idx0,const int idx1) const{
        for (const auto & var_val_pair : GetCex()){
          const auto & var_name = var_val_pair.first;
          auto pos = ts_.named_terms().find(var_name);
          assert(pos != ts_.named_terms().end());
          if(name_check!=var_name)
            continue;
          assert(var_val_pair.second.length()==val_check.length());
          auto val = var_val_pair.second;
          std::reverse(val.begin(), val.end());
          auto extract_val = val.substr(idx1,idx0-idx1+1);
          std::reverse(val_check.begin(), val_check.end());
          auto extract_val_check = val_check.substr(idx1,idx0-idx1+1);
          return (extract_val_check==extract_val);
      }
}
}