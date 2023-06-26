#include "frontends/property_if.h"
#include "filter.h"
#include "core/ts.h"
#include <fstream>
namespace pono {
AntFilter::AntFilter(const std::string filename, const std::string& filter, TransitionSystem &ts)
:ts_(ts){
    std::ifstream fCOI(filename);
    if (!fCOI.is_open())
      return;
    
    std::string varname;
    while(fCOI>>varname) {
      if(!filter.empty() && varname.find(filter) != 0)
       continue;
      // either module_name_filter_ is empty or varname start with module_name_filter_
      if(varname.find(filter) == 0)
        varname = varname.substr(filter.length());
      COI_to_consider_.emplace(varname,std::vector<std::pair<int,int>>());
      auto & vec_slices = COI_to_consider_.at(varname);

      int num_range;
      fCOI >> num_range;
      assert(num_range > 0);
      for (int idx = 0; idx < num_range; ++ idx) {
        int msb,lsb;
        fCOI>>msb>>lsb;
        vec_slices.push_back({msb,lsb});
      }
      
      std::string val;
      fCOI >> val;
      COI_value.emplace(varname, val);
    } // end of File
}


bool AntFilter::operator()(const std::string name_check, std::string val_check,const int idx0,const int idx1) const{
        for(const auto & coi: COI_to_consider_){
          const auto & var_name = coi.first;
          auto pos = ts_.named_terms().find(var_name);
          assert(pos != ts_.named_terms().end());
          if(name_check!=var_name)
            continue;
          auto pos_1 = COI_value.find(var_name);
          assert(pos_1 != COI_value.end());
          auto value = pos_1->second;
          assert(value.substr(0,2)=="#b");
          value = value.substr(2);
          assert(value.length()==val_check.length());
          std::reverse(value.begin(), value.end());
          auto extract_val = value.substr(idx1,idx0-idx1+1);
          std::reverse(val_check.begin(), val_check.end());
          auto extract_val_check = val_check.substr(idx1,idx0-idx1+1);
          return (extract_val_check==extract_val);
      }
}
}