
#include "railroad_parallel.h"
#include "digraph.hh"
#include "automata/ta_product.h"
#include "mtl/MTLFormula.h"
#include "utilities/Interval.h"
#include "visualization/ta_to_graphviz.h"
#include "ta_to_graph_symmetry/ta_to_graph_symmetry.hpp"
#include "ta_to_graph_symmetry/ta_conversor.hpp"

//#include "ta_to_graph_symmetry/automaton_compare.hpp"


using namespace tacos;

using Location   = automata::ta::Location<std::string>;
using TA         = automata::ta::TimedAutomaton<std::string, std::string>;
using Transition = automata::ta::Transition<std::string, std::string>;
using automata::AtomicClockConstraintT;
using F  = logic::MTLFormula<std::string>;
using AP = logic::AtomicProposition<std::string>;

std::tuple<automata::ta::TimedAutomaton<std::vector<std::string>, std::string>,
          logic::MTLFormula<std::string>,
          std::set<std::string>,
          std::set<std::string>>
create_parallel_problem(std::vector<Endpoint> trains)
{
    std::vector<TA>         automata;
    std::set<std::string>   controller_actions;
    std::set<std::string>   environment_actions;

    std::vector<F>          spec_disjuncts;

    
    for (std::size_t i = 1; i <= trains.size(); ++i) {

        const std::string clock        = "c_" + std::to_string(i);
        const std::string start_close  = "start_close_" + std::to_string(i);
        const std::string finish_close = "finish_close_" + std::to_string(i);
        const std::string start_open   = "start_open_" + std::to_string(i);
        const std::string finish_open  = "finish_open_" + std::to_string(i);

        std::cout<<"trains size: "<<trains.size()<<std::endl;
        controller_actions.insert({start_close, start_open, finish_close, finish_open});
        automata.push_back(
          TA{{Location{"OPEN"}, Location{"CLOSING"}, Location{"CLOSED"}, Location{"OPENING"}},
            {start_close, finish_close, start_open, finish_open},
            Location{"OPEN"},
            {Location{"OPEN"}, Location{"CLOSING"}, Location{"CLOSED"}, Location{"OPENING"}},
            {clock},
            {
              Transition(Location{"OPEN"}, start_close, Location{"CLOSING"}, {}, {clock}),
              Transition(Location{"CLOSING"},
                          finish_close,
                          Location{"CLOSED"},
                          {{clock, AtomicClockConstraintT<std::equal_to<Time>>(1)}},
                          {clock}),
              Transition(Location{"CLOSED"},
                          start_open,
                          Location{"OPENING"},
                          {{clock, AtomicClockConstraintT<std::greater_equal<Time>>(1)}},
                          {clock}),
              Transition(Location{"OPENING"},
                          finish_open,
                          Location{"OPEN"},
                          {{clock, AtomicClockConstraintT<std::equal_to<Time>>(1)}},
                          {clock}),
            }});
        std::set<std::string>   train_actions;
        std::set<Location>      train_locations;
        std::vector<Transition> train_transitions;
        const std::string i_t = std::to_string(i);
        // const auto     far = i == 1 ? Location{"FAR"} : Location{"FAR_BEHIND_" + std::to_string(i - 1)};
        // const Location near{"NEAR_" + i_s};
        // const Location in{"IN_" + i_s};
        // const Location behind{"BEHIND_" + i_s};
        // const Location far_behind{"FAR_BEHIND_" + i_s};
        const Location far{"FAR_"+ i_t};
        const Location near{"NEAR_" + i_t};
        const Location in{"IN_" + i_t};
        const Location behind{"BEHIND_" + i_t};
        const Location far_behind{"FAR_BEHIND_" + i_t};
        const std::string clock_train = "t_" + i_t;
        train_locations.insert({far, near, in, behind, far_behind});
        const std::string get_near{"get_near_" + i_t};
        const std::string enter{"enter_" + i_t};
        const std::string leave{"leave_" + i_t};
        const std::string travel{"travel_" + i_t};
        train_actions.insert({get_near, enter, leave, travel});
        train_transitions.push_back(
          Transition{far,
                    get_near,
                    near,
                    {{clock_train, AtomicClockConstraintT<std::equal_to<Time>>(trains[i - 1])}},
                    {clock_train}});

       

        train_transitions.push_back(
          Transition{near,
                    enter,
                    in,
                    {{clock_train, AtomicClockConstraintT<std::greater_equal<Time>>(0)},
                      {clock_train, AtomicClockConstraintT<std::less_equal<Time>>(1)}},
                    {clock_train}});
        train_transitions.push_back(Transition{
          in, leave, behind, {{clock_train, AtomicClockConstraintT<std::equal_to<Time>>(1)}}, {clock_train}});
        train_transitions.push_back(Transition{
          behind, travel, far_behind, {{clock_train, AtomicClockConstraintT<std::equal_to<Time>>(2)}}, {clock_train}});
        
        automata.push_back(TA{train_locations,
          train_actions,
          far,
          {far_behind},
          {clock_train},
          train_transitions});

          
        environment_actions.insert(std::begin(train_actions), std::end(train_actions));
        const auto finish_close_f = F{AP{finish_close}};
        const auto start_open_f   = F{AP{start_open}};
        const auto finish_open_f  = F{AP{finish_open}};
        const auto enter_f        = F{AP{enter}};
        const auto leave_f        = F{AP{leave}};
        const auto travel_f       = F{AP{travel}};
        spec_disjuncts.push_back(enter_f.dual_until(!finish_close_f)
                                || start_open_f.dual_until(!leave_f)
                                || travel_f.dual_until(!finish_open_f));
    }

    
    auto spec = spec_disjuncts[0];
    std::for_each(std::next(std::begin(spec_disjuncts)),
                  std::end(spec_disjuncts),
                  [&spec](auto &&spec_disjunct) { spec = spec || spec_disjunct; });
    for (std::size_t i = 1; i < automata.size(); i++) {
        visualization::ta_to_graphviz(automata[i - 1])
          .render_to_file(fmt::format("railroad{}_parallel_{}.pdf", trains.size(), i));
    }
    visualization::ta_to_graphviz(automata.back())
      .render_to_file(fmt::format("railroad{}_train_parallel.pdf", trains.size()));


    return std::make_tuple(automata::ta::get_product(automata),
                          spec,
                          controller_actions,
                          environment_actions);
}
