/*********************                                                  */
/*! \file indgen.cpp
** \verbatim
** Top contributors (to current version of this file):
**   Hongce Zhang
** This file is part of the pono project.
** Copyright (c) 2025 by the authors listed in the file AUTHORS
** in the top-level source directory) and their institutional affiliations.
** All rights reserved.  See the file LICENSE in the top-level source
** directory for licensing information.\endverbatim
**
** \brief Calling ABC to simplify aiger
**/


#include "engines/ic3ng.h"
#include "engines/ic3ng-support/debug.h"
#include "utils/container_shortcut.h"

// maybe fraig / if -g are not necessary at all ?
// you need to use write rather than &w
const std::string & script_template = R"***(
&r %s
&fraig
&dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; 
&fraig
&dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; 
&put ; if -g ; strash; &get ;
&dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; &dc2 ; 
&put
write %s
)***";

namespace pono
{

// &r input
// &fraig
// &dc2
// &put 
// if -g
// strash
// dc2

template<typename ... Args>
static std::string string_format( const std::string& format, Args ... args )
{
    int size_s = std::snprintf( nullptr, 0, format.c_str(), args ... ) + 1; // Extra space for '\0'
    if( size_s <= 0 ){ throw std::runtime_error( "Error during formatting." ); }
    auto size = static_cast<size_t>( size_s );
    std::unique_ptr<char[]> buf( new char[ size ] );
    std::snprintf( buf.get(), size, format.c_str(), args ... );
    return std::string( buf.get(), buf.get() + size - 1 ); // We don't want the '\0' inside
}

void IC3ng::aiger_simplify(const std::string & inputfname, const std::string & outfname) {
  { // write to abc_script
    auto script = string_format(script_template, inputfname.c_str(), outfname.c_str());
    std::ofstream fout("abc_script");
    if (!fout.is_open())
      throw PonoException("Unable to open abc_script for write.");
    fout << script;
  }
  std::system("yosys-abc -F 'abc_script' > abc_output.txt ");
}

} // end of namespace pono

