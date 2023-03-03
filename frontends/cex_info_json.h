/*********************                                                        */
/*! \file
 ** \verbatim
 ** Top contributors (to current version):
 **   Hongce ZHANG
 ** This file is part of the pono project.
 ** Copyright (c) 2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file LICENSE in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief
 **
 **
 **/

#pragma once

#include <fstream>
#include "json/json.hpp"

namespace pono {

struct CexInfoForEnvInvSyn {
  std::string cex_path_;
  std::string module_name_filter_;
  std::string module_name_removal_;
  std::vector<std::string> auxvar_removal_;
  std::vector<std::string> datapath_elements_;
  std::vector<std::string> COI_to_consider_;
  
  CexInfoForEnvInvSyn(const std::string & json_fname, const std::string & COI_fname) {
    std::ifstream f(json_fname);
    if(!f.is_open() )
        return ;
    nlohmann::json data = nlohmann::json::parse(f);
    data.at("CexPath").get_to(cex_path_);
    data.at("ModuleNameFilter").get_to(module_name_filter_);
    data.at("ModuleNameRemoval").get_to(module_name_removal_);
    data.at("AuxVarRemoval").get_to(auxvar_removal_);
    data.at("DataPathElements").get_to(datapath_elements_);

    std::ifstream fCOI(COI_fname);
    if (!fCOI.is_open())
      return;
    
    std::string varname;
    while(fCOI>>varname) {
      if(!module_name_filter_.empty() && varname.find(module_name_filter_) != 0)
       continue;
      // either module_name_filter_ is empty or varname start with module_name_filter_
      if(varname.find(module_name_removal_) == 0)
        varname = varname.substr(module_name_removal_.length());
      COI_to_consider_.push_back(varname);
    } // end of File

    fCOI.close();

  } // end of CexInfoForEnvInvSyn
};



}  // namespace pono

