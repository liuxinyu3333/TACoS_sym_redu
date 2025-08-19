
 #pragma once

 #include "automata/automata.h"
 #include "automata/ta.h"
 #include "mtl/MTLFormula.h"
 
 #include <set>
 #include <string>
 #include <tuple>
 #include <vector>
 
 std::tuple<tacos::automata::ta::TimedAutomaton<std::vector<std::string>, std::string>,
            tacos::logic::MTLFormula<std::string>,
            std::set<std::string>,
            std::set<std::string>>
 create_parallel_simple_problem(std::vector<tacos::Endpoint> trains);
 