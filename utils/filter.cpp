#include "frontends/property_if.h"
#include "filter.h"
#include "utils/term_analysis.h"
#include "core/ts.h"

namespace pono {
AntFilter::AntFilter(const std::string filename, TransitionSystem &ts, int step) : filename_(filename),ts_(ts), step_(step){
        // PropertyInterface pp = new PropertyInterface(filename_,ts_,step);
        PropertyInterface prop_inv(filename_,ts_,step);
        auto assumption = prop_inv.assumption;
        
        // auto assumption = assumptions_.at(i);
        get_predicates(ts.get_solver(),assumption,out,false,true,true);
          
}

bool AntFilter::operator()(const smt::Term &n) const{
        for (const auto & it: out){
          if (it->to_string() == n ->to_string()){
            return true;
          }
    }
    return false;
}
}