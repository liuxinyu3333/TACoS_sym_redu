/***************************************************************************
 *  test_railroad.cpp - A railroad example
 *
 *  Created:   Mon  1 Mar 17:18:27 CET 2021
 *  Copyright  2021  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/


#define SPDLOG_ACTIVE_LEVEL SPDLOG_LEVEL_ERROR

#include "automata/automata.h"
#include "automata/ta.h"
#include "automata/ta_product.h"
#include "automata/ta_regions.h"
#include "heuristics_generator.h"
#include "mtl/MTLFormula.h"
#include "mtl_ata_translation/translator.h"
#include "railroad.h"
#include "railroad_parallel.h"
#include "railroad_parallel_simple.h"
#include "search/canonical_word.h"
#include "search/create_controller.h"
#include "search/heuristics.h"
#include "search/search.h"
#include "search/search_tree.h"
#include "search/synchronous_product.h"
#include "search/ta_adapter.h"
#include "visualization/ta_to_graphviz.h"
#include "visualization/tree_to_graphviz.h"
#include "ta_to_graph_symmetry/ata_conversor.hpp"
#include "ta_to_graph_symmetry/ta_conversor.hpp"
#include "ta_to_graph_symmetry/automaton_compare.hpp"
#include "ta_to_graph_symmetry/ta_to_graph_symmetry.hpp"
#include "digraph.hh"
#include <cstdlib>


#include <fmt/format.h>
#include <fmt/ostream.h>
#include <spdlog/common.h>
#include <spdlog/spdlog.h>

#include <catch2/benchmark/catch_benchmark.hpp>
#include <catch2/catch_test_macros.hpp>
#include <catch2/generators/catch_generators.hpp>
#include <iterator>
#include <fstream>

#undef TRUE

namespace {

using namespace tacos;

using Location   = automata::ta::Location<std::string>;
using TA         = automata::ta::TimedAutomaton<std::string, std::string>;
using Transition = automata::ta::Transition<std::string, std::string>;
using F          = logic::MTLFormula<std::string>;
using AP         = logic::AtomicProposition<std::string>;
using search::NodeLabel;
using TreeSearch =
  search::TreeSearch<automata::ta::Location<std::vector<std::string>>, std::string>;

TEST_CASE("Railroad", "[railroad]")
{
	const auto &[plant, spec, controller_actions, environment_actions] = create_parallel_simple_problem({2,2});
	const auto   num_crossings                                         = 1;
	std::set<AP> actions;
	std::set_union(begin(controller_actions),
	               end(controller_actions),
	               begin(environment_actions),
	               end(environment_actions),
	               inserter(actions, end(actions)));
	CAPTURE(spec);

	std::cout<< "spec: "<<spec<<std::endl;
	auto ata = mtl_ata_translation::translate(spec, actions);


	CAPTURE(plant);
	CAPTURE(ata);
	const unsigned int K = std::max(plant.get_largest_constant(), spec.get_largest_constant());
	TreeSearch         search{&plant,
                    &ata,
                    controller_actions,
                    environment_actions,
                    K,
                    true,
                    true,
                    generate_heuristic<TreeSearch::Node>()};
	search.build_tree(true);
	CHECK(search.get_root()->label == NodeLabel::TOP);
#ifdef HAVE_VISUALIZATION
	visualization::search_tree_to_graphviz(*search.get_root(), true)
	  .render_to_file(fmt::format("railroad{}.svg", num_crossings));
	visualization::ta_to_graphviz(controller_synthesis::create_controller(
	                                search.get_root(), controller_actions, environment_actions, 2),
	                              false)
	  .render_to_file(fmt::format("railroad{}_controller.pdf", num_crossings));
#endif
}

TEST_CASE("Railroad crossing benchmark", "[.benchmark][railroad]")
{
	spdlog::set_level(spdlog::level::debug);
	spdlog::set_pattern("%t %v");
	auto distances = GENERATE(
	  values({std::vector<Endpoint>{2}, std::vector<Endpoint>{2, 2}, std::vector<Endpoint>{2, 4}}));
	const auto   num_crossings       = distances.size();
	const auto   problem             = create_crossing_problem(distances);
	auto         plant               = std::get<0>(problem);
	auto         spec                = std::get<1>(problem);
	auto         controller_actions  = std::get<2>(problem);
	auto         environment_actions = std::get<3>(problem);
	std::set<AP> actions;
	std::set_union(begin(controller_actions),
	               end(controller_actions),
	               begin(environment_actions),
	               end(environment_actions),
	               inserter(actions, end(actions)));
	CAPTURE(spec);
	auto ata = mtl_ata_translation::translate(spec, actions);
	
	
	CAPTURE(plant);
	CAPTURE(ata);
	const unsigned int K = std::max(plant.get_largest_constant(), spec.get_largest_constant());

	//	auto weight_plant = GENERATE(-5, -1, 0, 1, 10);
	//	auto weight_canonical_words = GENERATE(-5, 0, 5);
	// auto weight_plant           = GENERATE(8, 10, 12, 15);
	// auto weight_canonical_words = GENERATE(4, 6, 10, 15);
	auto weight_plant           = 12;
	auto weight_canonical_words = 10;
	BENCHMARK(
	  fmt::format("Run search with weight_plant={}, weight_canonical_words={}, distances=({})",
	              weight_plant,
	              weight_canonical_words,
	              fmt::join(distances, ", ")))
	{
		TreeSearch search{&plant,
		                  &ata,
		                  controller_actions,
		                  environment_actions,
		                  K,
		                  true,
		                  true,
		                  generate_heuristic<TreeSearch::Node>(weight_canonical_words,
		                                                       weight_plant,
		                                                       environment_actions)};

		search.build_tree(true);
		CHECK(search.get_root()->label == NodeLabel::TOP);
#ifdef HAVE_VISUALIZATION
		visualization::search_tree_to_graphviz(*search.get_root(), true)
		  .render_to_file(fmt::format("railroad{}.svg", num_crossings));
		visualization::ta_to_graphviz(controller_synthesis::create_controller(
		                                search.get_root(), controller_actions, environment_actions, 2),
		                              false)
		  .render_to_file(fmt::format("railroad{}_controller.pdf", num_crossings));
#endif
	};
}
TEST_CASE("TA Graph generation Only", "[graph_ta]") {
	using TA 				 =  tacos::automata::ta::TimedAutomaton<std::string, std::string>;
	const std::string clock  = "c";
	auto ta = TA{{Location{"OPEN"}, Location{"CLOSING"}},
		     {"start_close", "finish"},
		     Location{"OPEN"},
		     {Location{"OPEN"}, Location{"CLOSING"}},
		     {clock},
		     {
		       Transition(Location{"OPEN"}, "start_close", Location{"CLOSING"}, {{clock, tacos::automata::AtomicClockConstraintT<std::equal_to<Time>>(1)}}, {clock}),
		       Transition(Location{"CLOSING"},
		                  "finish",
		                  Location{"OPEN"},
		                  {{clock, tacos::automata::AtomicClockConstraintT<std::greater_equal<Time>>(1)}},
		                  {clock}),
		  
		     }
			};
	auto [g1, taTrans_to_subgraph ] = automata::ta::buildGraphFromTA(ta, {"OPEN"});
	std::cout<< "看看能不能打印出来： "<<std::endl;
	convertToBlissDigraph(g1).graph;
	g1.exportGraphToDot("ta.dot");
	//g2.exportGraphToDot("ata.dot");
	try
	{
		g1.generateGraphImage("ta.dot", "ta.png");
		//g2.generateGraphImage("ata.dot", "ata.png");
	
	} catch (const std::exception &ex) {
		std::cerr << "错误：" << ex.what() << std::endl;
	}
			 
	

}
TEST_CASE("spec gerneration", "[spec]") {
	
    const std::string finish_close = "finish_close";
    const std::string start_open   = "start_open";
	const std::string enter{"enter_"};
	const std::string leave{"leave_"};
	const auto finish_close_f = F{AP{finish_close}};
	const auto start_open_f   = F{AP{start_open}};
	const auto enter_f        = F{AP{enter}};
	const auto leave_f        = F{AP{leave}};
	std::set<AP> actions;

	std::set<std::string>   controller_actions  = {start_open, finish_close};
	std::set<std::string>   environment_actions = {enter, leave};
	std::set_union(begin(controller_actions), end(controller_actions),
	               begin(environment_actions), end(environment_actions),
	               inserter(actions, end(actions)));
	F spec = enter_f.dual_until(!finish_close_f) || start_open_f.dual_until(!leave_f) ;
	auto ata = mtl_ata_translation::translate(spec, actions);
	std::cout<<ata<<std::endl;
	auto g2 = automata::ata::buildGraphFromATA(ata, controller_actions);
	g2.exportGraphToDot("ata.dot");
	g2.generateGraphImage("ata.dot", "ata.png");
}

TEST_CASE("ATA Graph generation Only", "[graph ata]") {
	const auto   problem = create_crossing_problem({2,4});
	auto         spec    = std::get<1>(problem);
	auto         controller_actions  = std::get<2>(problem);
	auto         environment_actions = std::get<3>(problem);
	std::set<AP> actions;
	std::set_union(begin(controller_actions), end(controller_actions),
	               begin(environment_actions), end(environment_actions),
	               inserter(actions, end(actions)));
	auto ata = mtl_ata_translation::translate(spec, actions);
	auto g2 = automata::ata::buildGraphFromATA(ata, controller_actions);
	std::cout<< "ATA转化为Graph： "<<std::endl;
	g2.exportGraphToDot("ata_g.dot");
	try
	{
		g2.generateGraphImage("ata_g.dot", "ata_g.png");
	
	} catch (const std::exception &ex) {
		std::cerr << "错误：" << ex.what() << std::endl;
	}


}
TEST_CASE("Graph orbit Only", "[graph ata orbit]") {
	const auto   problem = create_parallel_problem({2,2});
	auto         ta = std::get<0>(problem);
	auto         spec    = std::get<1>(problem);
	auto         controller_actions  = std::get<2>(problem);
	auto         environment_actions = std::get<3>(problem);
	std::set<AP> actions;
	std::set_union(begin(controller_actions), end(controller_actions),
	               begin(environment_actions), end(environment_actions),
	               inserter(actions, end(actions)));
	auto ata = mtl_ata_translation::translate(spec, actions);
	auto [g1, taTrans_to_subgraph]= automata::ta::buildGraphFromTA(ta, controller_actions);

	auto g2 = automata::ata::buildGraphFromATA(ata, controller_actions);
	auto bliss_g1 = convertToBlissDigraph(g1).graph;
	auto [g1_orbits, g1_nodes_to_rep] = get_Orbits(bliss_g1);
	//printMiddelOrbits(g1_orbits, g1);
	auto bliss_g2 = convertToBlissDigraph(g2).graph;
	auto [g2_orbits, g2_nodes_to_rep] = get_Orbits(bliss_g2);
	//printMiddelOrbits(g2_orbits, g2);

	std::cout<<ata<<std::endl;
	auto g1_merge = mergeOrbitsInGraph(g1, g1_orbits);
	auto g2_merge = mergeOrbitsInGraph(g2, g2_orbits);

	// auto ta_re_ptr = tacos::automata::ta::buildTAFromGraph(g1_merge);
	auto ata_re_ptr = tacos::automata::ata::buildATAFromGraph(std::get<0>(g2_merge));
	// std::cout << "ta_re_ptr: " << *ta_re_ptr << std::endl;
	std::cout << "ata_re_ptr: " << *ata_re_ptr << std::endl;

	std::cout<< "======================"<<std::endl;
	// auto action_orbits_ata = get_action_Orbits(g2_orbits,g2);
	
	// printOrbits(action_orbits_ata, g2);
}
TEST_CASE("equal test", "[test_equal]") {
	auto distances = GENERATE(
	  values({ std::vector<Endpoint>{2}}));

	//std::vector<Endpoint>{2}, std::vector<Endpoint>{2, 2}, std::vector<Endpoint>{2, 4}
	// 只执行转换和打印，不进行基准测试
	const auto   problem = create_crossing_problem(distances);
	auto 		 ta = std::get<0>(problem);
	auto         spec    = std::get<1>(problem);
	auto         controller_actions  = std::get<2>(problem);
	auto         environment_actions = std::get<3>(problem);
	std::cout<<"spec : "<<spec<<std::endl;
	std::set<AP> actions;
	std::set_union(begin(controller_actions), end(controller_actions),
	               begin(environment_actions), end(environment_actions),
	               inserter(actions, end(actions)));

	auto ata = mtl_ata_translation::translate(spec, actions);
	auto g2 = automata::ata::buildGraphFromATA(ata, controller_actions);	
	auto [g1, taTrans_to_subgraph ]= automata::ta::buildGraphFromTA(ta, controller_actions);
	auto ata_re = automata::ata::buildATAFromGraph(g2);
	
	auto ta_ptr_and_map = automata::ta::buildTAFromGraph(g1);
    auto ta_re = std::get<0>(ta_ptr_and_map);
    
	std::cout << "ATA equal?: " << are_ata_equal(*ata_re, ata)<< std::endl;
	
	std::cout << "TA equal?: " << are_ta_equal(*ta_re, ta)<< std::endl;
	CAPTURE(*ta_re);
	CAPTURE(*ata_re);
	const unsigned int K = std::max(ta_re->get_largest_constant(), spec.get_largest_constant());
	TreeSearch         search{ta_re.get(),
					ata_re.get(),
                    controller_actions,
                    environment_actions,
                    K,
                    true,
                    true,
                    generate_heuristic<TreeSearch::Node>()
					};
	search.build_tree(true);
	CHECK(search.get_root()->label == NodeLabel::TOP);
#ifdef HAVE_VISUALIZATION
	visualization::search_tree_to_graphviz(*search.get_root(), true)
	  .render_to_file(fmt::format("railroad{}.svg", 198));
	visualization::ta_to_graphviz(controller_synthesis::create_controller(
									search.get_root(), controller_actions, environment_actions, 2),
								  false)
	  .render_to_file(fmt::format("railroad{}_controller.pdf", 198));
#endif


}

TEST_CASE("symmetry reduce", "[symmetry]") {
	auto distances = GENERATE(
		values({ std::vector<Endpoint>{2,2}}));
  
	  //std::vector<Endpoint>{2}, std::vector<Endpoint>{2, 2}, std::vector<Endpoint>{2, 4}
	  // 只执行转换和打印，不进行基准测试
	  //const auto   problem = create_parallel_problem(distances);
	  const auto   problem = create_crossing_problem(distances);
	  auto 		   ta = std::get<0>(problem);
	  auto         spec    = std::get<1>(problem);
	  auto         controller_actions  = std::get<2>(problem);
	  auto         environment_actions = std::get<3>(problem);
	  std::cout<<"spec : "<<spec<<std::endl;
	  std::set<AP> actions;
	  std::set_union(begin(controller_actions), end(controller_actions),
					 begin(environment_actions), end(environment_actions),
					 inserter(actions, end(actions)));
  
  
  
  
  
	  std::cout<<"actions size: "<<actions.size()<<std::endl;
	  auto ata = mtl_ata_translation::translate(spec, actions);
  
	  auto result1 = get_symmetry_result(ta,ata,controller_actions );
	  auto re_ta = std::get<0>(result1);
	  auto re_ata = std::get<1>(result1);
	  //auto ta_map_ata1 = std::get<2>(result1);

	  	
	// using ta_class = tacos::automata::ta::TimedAutomaton<std::vector<std::string>, std::string>;
	// using ata_class = tacos::automata::ata::AlternatingTimedAutomaton<tacos::logic::MTLFormula<std::string>, tacos::logic::AtomicProposition<std::string>>;

	// //auto tran_ta = action_orbits_ta1.automata->get_transitions();
	// auto re_ta = std::get<std::shared_ptr<ta_class>>(action_orbits_ta1.automata);


	

	// std::cout << "re_ta : "<< *re_ta << std::endl;


	// auto re_ata = std::get<std::shared_ptr<ata_class>>(action_orbits_ata1.automata);
	// std::cout << "re_ata : "<< *re_ata<< std::endl;
	//auto re_ta = automata::ta::buildTAFromGraph(action_orbits_ta1.graph_simplified);
	//auto re_ata = automata::ata::buildATAFromGraph(action_orbits_ata1.graph_simplified);

	// auto iterator = re_ata->get_transitions().begin();
	// for (iterator )
	// for (const auto& tran : transitions) {
	// 	auto form = tran.getFormula();
	// 	if (tran.source_ == source_loc.value() && tran.symbol_ == actionOpt.value() && *form !=*t_formula) {
	// 		t_formula = create_disjunction<LocationT>(std::move(tran.getFormula()), std::move(t_formula));
	// 	}
	// }


	std::cout<< "======ta===transitions===="<<std::endl;
	std::cout<< re_ta->get_transitions().size() << std::endl;
	std::cout<< ta.get_transitions().size() << std::endl;
	std::cout<< "======ata===transitions===="<<std::endl;

	std::cout<< re_ata->get_transitions().size() << std::endl;
	std::cout<< ata.get_transitions().size() << std::endl;

	std::cout<< "======ta===action===="<<std::endl;
	std::cout<< re_ta->get_alphabet().size() << std::endl;
	std::cout<< ta.get_alphabet().size() << std::endl;

	std::cout<< "======ata===action===="<<std::endl;
	std::cout<< re_ata->get_alphabet().size() << std::endl;
	std::cout<< ata.get_alphabet().size() << std::endl;




	CAPTURE(*re_ta);
	CAPTURE(*re_ata);
	const unsigned int K = std::max(re_ta->get_largest_constant(), spec.get_largest_constant());
	TreeSearch         search{re_ta.get(),
                    re_ata.get(),
                    controller_actions,
                    environment_actions,
                    K,
                    true,
                    true,
                    generate_heuristic<TreeSearch::Node>(),
					};
	search.build_tree(true);
	CHECK(search.get_root()->label == NodeLabel::TOP);
#ifdef HAVE_VISUALIZATION
	visualization::search_tree_to_graphviz(*search.get_root(), true)
	  .render_to_file(fmt::format("railroad{}.svg", 10011));
	visualization::ta_to_graphviz(controller_synthesis::create_controller(
									search.get_root(), controller_actions, environment_actions, 2),
								  false)
	  .render_to_file(fmt::format("railroad{}_controller.pdf", 10011));
#endif
	

}

TEST_CASE("symmetry reduce simple", "[symmetry simple]") {
	auto distances = GENERATE(
		values({ std::vector<Endpoint>{2,2}}));
  
	  //std::vector<Endpoint>{2}, std::vector<Endpoint>{2, 2}, std::vector<Endpoint>{2, 4}
	  // 只执行转换和打印，不进行基准测试
	  const auto   problem = create_parallel_problem(distances);
	  //const auto   problem = create_crossing_problem(distances);
	  auto 		   ta = std::get<0>(problem);
	  auto         spec    = std::get<1>(problem);
	  auto         controller_actions  = std::get<2>(problem);
	  auto         environment_actions = std::get<3>(problem);
	  std::cout<<"spec : "<<spec<<std::endl;
	  std::set<AP> actions;
	  std::set_union(begin(controller_actions), end(controller_actions),
					 begin(environment_actions), end(environment_actions),
					 inserter(actions, end(actions)));
  
  
	  
  
  
	  std::cout<<"actions size: "<<actions.size()<<std::endl;
	  auto ata = mtl_ata_translation::translate(spec, actions);
  
	  auto result1 = get_symmetry_result(ta,ata,controller_actions );
	  auto re_ta = std::get<0>(result1);
	  auto re_ata = std::get<1>(result1);
	  auto ta_loc_orbits = std::get<2>(result1);
	  auto transition_orbits = std::get<3>(result1);
	  //auto ta_map_ata1 = std::get<2>(result1);

	  	
	// using ta_class = tacos::automata::ta::TimedAutomaton<std::vector<std::string>, std::string>;
	// using ata_class = tacos::automata::ata::AlternatingTimedAutomaton<tacos::logic::MTLFormula<std::string>, tacos::logic::AtomicProposition<std::string>>;

	// //auto tran_ta = action_orbits_ta1.automata->get_transitions();
	// auto re_ta = std::get<std::shared_ptr<ta_class>>(action_orbits_ta1.automata);


	

	// //std::cout << "re_ta : "<< *re_ta << std::endl;


	// auto re_ata = std::get<std::shared_ptr<ata_class>>(action_orbits_ata1.automata);
	std::cout<< "======ta===loc===="<<std::endl;
	std::cout<< re_ta->get_locations().size() << std::endl;
	std::cout<< ta.get_locations().size() << std::endl;
	std::cout<< "======ata===loc===="<<std::endl;
	std::cout<< re_ata->get_final_locations().size() << std::endl;
	std::cout<< ata.get_final_locations().size() << std::endl;

	std::cout<< "======ta===transitions===="<<std::endl;
	std::cout<< re_ta->get_transitions().size() << std::endl;
	std::cout<< ta.get_transitions().size() << std::endl;
	std::cout<< "======ata===transitions===="<<std::endl;

	std::cout<< re_ata->get_transitions().size() << std::endl;
	std::cout<< ata.get_transitions().size() << std::endl;

	std::cout<< "======ta===action===="<<std::endl;
	std::cout<< re_ta->get_alphabet().size() << std::endl;
	std::cout<< ta.get_alphabet().size() << std::endl;

	std::cout<< "======ata===action===="<<std::endl;
	std::cout<< re_ata->get_alphabet().size() << std::endl;
	std::cout<< ata.get_alphabet().size() << std::endl;

	std::cout<< "======ta===action===="<<std::endl;
	std::cout<< re_ta->get_final_locations().size() << std::endl;
	std::cout<< ta.get_final_locations().size() << std::endl;
	std::cout<< "======ata===action===="<<std::endl;
	std::cout<< re_ata->get_final_locations().size() << std::endl;
	std::cout<< ata.get_final_locations().size() << std::endl;

	// visualization::ta_to_graphviz(ta)
	// .render_to_file(fmt::format("ta_example.pdf"));
    // visualization::ta_to_graphviz(*re_ta)
	// .render_to_file(fmt::format("re_ta_example.pdf"));



	// for (const auto & loc_o: ta_loc_orbits){
	// 	std::cout<<""<<std::endl;
	// 	std::cout<<"ta loc rep: "<<loc_o.first<<std::endl;
	// 	for (const auto &loc_c: loc_o.second){
	// 		std::cout<<"ta loc content: "<<loc_c<<std::endl;
	// 	}	
	// }
	// std::cout<<""<<std::endl;
	// for (const auto & loc_o: transition_orbits){
	// 	std::cout<<""<<std::endl;
	// 	std::cout<<"ta trans rep: "<<loc_o.first<<std::endl;
	// 	for (const auto &loc_c: loc_o.second){
	// 		std::cout<<"ta trans content: "<<loc_c<<std::endl;
	// 	}	
	// }
	// std::cout<<""<<std::endl;


	// std::cout<<re_ata->get_initial_location()<<std::endl;

	// std::cout<<re_ta->get_initial_location()<<std::endl;
	// }
	// for (const auto &ac: re_ta->get_alphabet()){
	// 	std::cout<<ac<<std::endl;
	// }
	// for (const auto &ac: re_ata->get_alphabet()){
	// 	std::cout<<ac<<std::endl;
	// }

	// CAPTURE(*re_ta);
	// CAPTURE(*re_ata);
	// const unsigned int K = std::max(re_ta->get_largest_constant(), spec.get_largest_constant());
	// TreeSearch         search{re_ta.get(),
    //                 re_ata.get(),
    //                 controller_actions,
    //                 environment_actions,
    //                 K,
    //                 true,
    //                 true,
    //                 generate_heuristic<TreeSearch::Node>(),
	// 				};
	// search.build_tree(false);
	// CHECK(search.get_root()->label == NodeLabel::TOP);
	// using TreeSearch_sym  = search::TreeSearch<automata::ta::Location<
	// 											std::vector<std::string>>, 
	// 											std::string, 
	// 											std::string,
	// 											false,
	// 											automata::ta::TimedAutomaton<std::vector<std::string>, std::string>,
	// 											false,
	// 											true>;
	// TreeSearch_sym    var{&ta,
	// 	&ata,
	// 	controller_actions,
	// 	environment_actions,
	// 	K,
	// 	true,
	// 	true,
	// 	generate_heuristic<TreeSearch::Node>(),
	// 	std::shared_ptr<TreeSearch::Node>(search.get_root()),
	// 	true,
	// 	ta_loc_orbits,
	// 	transition_orbits,
	// 	};
	// var.build_tree(false);
	// CHECK(var.get_root()->label == NodeLabel::TOP);
// #ifdef HAVE_VISUALIZATION
// 	visualization::search_tree_to_graphviz(*search.get_root(), true)
// 	  .render_to_file(fmt::format("railroad{}.svg", 10011));
// 	visualization::ta_to_graphviz(controller_synthesis::create_controller(
// 									search.get_root(), controller_actions, environment_actions, 2),
// 								  false)
// 	  .render_to_file(fmt::format("railroad{}_controller.pdf", 10011));
// #endif
	

}

TEST_CASE("thesis example", "[thesis]") {
using TA 				 =  tacos::automata::ta::TimedAutomaton<std::string, std::string>;
	const std::string clock  = "c";
	auto ta = TA{{Location{"l0"}, Location{"l1"}},
		     {"a", "e"},
		     Location{"l0"},
		     {Location{"l0"}, Location{"l1"}},
		     {clock},
		     {
		       Transition(Location{"l0"}, "e", Location{"l1"}, {{clock, tacos::automata::AtomicClockConstraintT<std::equal_to<Time>>(1)}}, {clock}),
		       Transition(Location{"l0"},
		                  "a",
		                  Location{"l0"},
		                  {{clock, tacos::automata::AtomicClockConstraintT<std::greater_equal<Time>>(0)}},
		                  {clock}),
		  
		     }
			};
	const std::string action_a = "a";
	const std::string action_e = "e";
	//tacos::logic::AtomicProposition<std::string> ap("action_e");
	const auto phi = tacos::logic::MTLFormula<std::string>(tacos::logic::AtomicProposition<std::string>(action_e));
	auto spec = phi|| tacos::logic::finally(phi);
    auto ata = mtl_ata_translation::translate(spec, {action_a, action_e});  
	std::cout << ata <<std::endl;
	auto g2 = automata::ata::buildGraphFromATA(ata, {"a"});
	auto [g1, taTrans_to_subgraph ] = automata::ta::buildGraphFromTA(ta, {"a"});
	std::cout<< "看看能不能打印出来： "<<std::endl;
	convertToBlissDigraph(g1).graph;
	g1.exportGraphToDot("ta.dot");
	g2.exportGraphToDot("ata.dot");
	try
	{
		g1.generateGraphImage("ta.dot", "ta.png");
		g2.generateGraphImage("ata.dot", "ata.png");
	
	} catch (const std::exception &ex) {
		std::cerr << "错误：" << ex.what() << std::endl;
	}
			 
}

TEST_CASE("ATA Graph Conversion Only", "[ata_graph]") {
    auto distances = GENERATE(
      values({ std::vector<Endpoint>{2,2}}));

    //std::vector<Endpoint>{2}, std::vector<Endpoint>{2, 2}, std::vector<Endpoint>{2, 4}
    // 只执行转换和打印，不进行基准测试
    const auto   problem = create_parallel_problem(distances);
	auto 		 ta = std::get<0>(problem);
    auto         spec    = std::get<1>(problem);
    auto         controller_actions  = std::get<2>(problem);
    auto         environment_actions = std::get<3>(problem);
	std::cout<<"spec : "<<spec<<std::endl;
    std::set<AP> actions;
    std::set_union(begin(controller_actions), end(controller_actions),
                   begin(environment_actions), end(environment_actions),
                   inserter(actions, end(actions)));





    std::cout<<"actions size: "<<actions.size()<<std::endl;
    auto ata = mtl_ata_translation::translate(spec, actions);

	//std::cout << "ATA: " << std::endl;
	
	//std::cout << ata << std::endl;
    // 添加控制台输出
    std::cout << "=============" << distances.size() << " gates =============" << std::endl;
	auto g2 = automata::ata::buildGraphFromATA(ata, controller_actions);	
	auto [g1, taTrans_to_subgraph ]= automata::ta::buildGraphFromTA(ta, controller_actions);

	auto [g_merge, ta_to_merged, ata_to_merged, merged_to_ta, merged_to_ata, merged_to_ta_action, merged_to_ata_action] = mergeGraphs(g1, g2);
	auto bliss_g_merge = convertToBlissDigraph(g_merge).graph;
	auto [g_merge_orbits, g_merge_nodes_to_rep] = get_Orbits(bliss_g_merge);
	std::cout << "Merged graph nodes: " << g_merge.getNodes().size() << std::endl;

	auto g_r = mergeOrbitsInGraph(g_merge, g_merge_orbits);
	// for (const auto& node : g_r.getNodes()){
	// 	if (node.type == NodeType::Controller_Action||node.type == NodeType::Environment_Action){
	// 		std::cout <<"node id: " << node.id << " label: ";
	// 		std::visit([](auto &&val) {
	// 			std::cout << val << std::endl;
	// 		}, node.label);
	// 	}
	// }
	// std::cout << "ta transition size: " << ta.get_transitions().size() << std::endl;
	// std::cout << "subgraph size: " << taTrans_to_subgraph.size() << std::endl;

	// auto ata_re = automata::ata::buildATAFromGraph(g2);
	// auto ta_re = automata::ta::buildTAFromGraph(g1);
	// std::cout << "============= transform finish =============" << std::endl;
	// std::cout << "ta_re and ta is equal: " << are_ta_equal(ta,*ta_re) << std::endl;	
	// std::cout << "ata_re and ata is equal: " << are_ata_equal(ata,*ata_re) << std::endl;	

	auto bliss_g1 = convertToBlissDigraph(g1).graph;
	auto bliss_g2 = convertToBlissDigraph(g2).graph;
	std::cout << "g1 nodes: " << g1.getNodes().size() << std::endl;
	std::cout << "g2 nodes: " << g2.getNodes().size() << std::endl;
	std::cout << "g1 bliss nodes: " << bliss_g1->get_nof_vertices() << std::endl;
	std::cout << "g2 bliss nodes: " << bliss_g2->get_nof_vertices() << std::endl;

	// for(const auto& node : g1.getNodes()){
	// 	g1.printNode(node);
	// 	//std::cout << "color: " << node.color << std::endl;
	// }

	auto [g1_orbits, g1_nodes_to_rep] = get_Orbits(bliss_g1);
	auto [g2_orbits, g2_nodes_to_rep] = get_Orbits(bliss_g2);
//⬆ ta->graph g1->bliss g1->orbits of ta; ata ->graph g2->bliss g2->orbits of ata



	// 	}
	// } 
	
	// int count=0;
	// for (auto& kv : g1_orbits){
	// 	auto k = kv.first;

	// 	if (k.type == NodeType::TAMiddleNode){
	// 		std::cout <<"rep middel node id: " << node.id <<" label: ";
	// 		std::visit([](auto &&val) {
	// 			std::cout << val << std::endl;
	// 		}, k.label);
	// 		for (auto& v : kv.second){
	// 			std::cout <<"node id: " << node.id <<" label: ";
	// 			std::visit([](auto &&val) {
	// 				std::cout << val << std::endl;
	// 			}, v.label);
	// 		}
			
	// 		count++;
	// 	}
	// }
	//std::cout << "action num: " << count << std::endl;

	// auto ta_test= automata::ta::buildTAFromGraph(g1_re);
	// std::cout << "ta_test alphabet: " << ta_test->get_alphabet().size() << std::endl;


	// for (const auto& trans : ta_test->get_transitions()){
	// 	std::cout<<trans.second<<std::endl;
	// }
	// auto trans_orbits = compute_transition_orbits(g1_nodes_to_rep, taTrans_to_subgraph);
	// for (const auto& tran: trans_orbits){
	// 	std::cout<<tran.first << std::endl;
	// }
	// std::cout << "Transition: " << ta.get_transitions().size() << std::endl;
	// std::cout<<"transition num: "<<trans_orbits.size()<<std::endl;
	
	

	std::cout<< "==========action orbits============="<<std::endl;

	auto action_orbits_ta = get_action_Orbits(g1_orbits,g1);
	auto action_orbits_ata = get_action_Orbits(g2_orbits,g2);


 	auto result1 = get_action_Orbits_map(ta,ata,controller_actions );
	auto action_orbits_ta1 = std::get<0>(result1);
	auto action_orbits_ata1 = std::get<1>(result1);
	auto ta_map_ata1 = std::get<2>(result1);
	std::cout<< "看看结果： "<<ta_map_ata1.size() << std::endl;
	for (auto& a: ta_map_ata1){
		std::cout<< "ta : " << tacos::automata::ata::formula_to_string(a.first) << std::endl;
		
		std::cout<< "ata : " << tacos::automata::ata::formula_to_string(a.second) << std::endl;

		std::cout<< " "<< std::endl;
			
	}
	
	//g2.printNodes();
	
	using ta_class = tacos::automata::ta::TimedAutomaton<std::vector<std::string>, std::string>;
	using ata_class = tacos::automata::ata::AlternatingTimedAutomaton<tacos::logic::MTLFormula<std::string>, tacos::logic::AtomicProposition<std::string>>;

	//auto tran_ta = action_orbits_ta1.automata->get_transitions();
	auto re_ta = std::get<std::shared_ptr<ta_class>>(action_orbits_ta1.automata);




	//std::cout << "re_ta : "<< *re_ta << std::endl;


	auto re_ata = std::get<std::shared_ptr<ata_class>>(action_orbits_ata1.automata);
	std::cout << "re_ata : "<< *re_ata<< std::endl;
	//auto re_ta = automata::ta::buildTAFromGraph(action_orbits_ta1.graph_simplified);
	//auto re_ata = automata::ata::buildATAFromGraph(action_orbits_ata1.graph_simplified);
	std::cout<< "======ta======="<<std::endl;
	std::cout<< re_ta->get_transitions().size() << std::endl;
	std::cout<< ta.get_transitions().size() << std::endl;
	std::cout<< "======ata======="<<std::endl;

	std::cout<< re_ata->get_transitions().size() << std::endl;
	std::cout<< ata.get_transitions().size() << std::endl;

	CAPTURE(*re_ta);
	CAPTURE(*re_ata);
// 	const unsigned int K = std::max(re_ta->get_largest_constant(), spec.get_largest_constant());
// 	TreeSearch         search{re_ta.get(),
//                     re_ata.get(),
//                     controller_actions,
//                     environment_actions,
//                     K,
//                     true,
//                     true,
//                     generate_heuristic<TreeSearch::Node>(),
// 					ta_map_ata1};
// 	search.build_tree(true);
// 	CHECK(search.get_root()->label == NodeLabel::TOP);
// #ifdef HAVE_VISUALIZATION
// 	visualization::search_tree_to_graphviz(*search.get_root(), true)
// 	  .render_to_file(fmt::format("railroad{}.svg", 100000));
// 	visualization::ta_to_graphviz(controller_synthesis::create_controller(
// 									search.get_root(), controller_actions, environment_actions, 2),
// 								  false)
// 	  .render_to_file(fmt::format("railroad{}_controller.pdf", 100000));
// #endif
	
 }
} // namespace
