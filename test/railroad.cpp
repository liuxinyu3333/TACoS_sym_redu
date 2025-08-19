/***************************************************************************
 *  railroad.cpp - Utility functions for railroad test scenario
 *
 *  Created: Tue 20 Apr 2021 13:00:42 CEST 13:00
 *  Copyright  2021  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/



#include "railroad.h"
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
create_crossing_problem(std::vector<Endpoint> distances)
{
	std::vector<TA>         automata;
	std::set<std::string>   controller_actions;
	std::set<std::string>   environment_actions;
	std::set<std::string>   train_actions;
	std::set<Location>      train_locations;
	std::vector<Transition> train_transitions;
	std::vector<F>          spec_disjuncts;
	for (std::size_t i = 1; i <= distances.size(); ++i) {
		const std::string clock        = "c_" + std::to_string(i);
		const std::string start_close  = "start_close_" + std::to_string(i);
		const std::string finish_close = "finish_close_" + std::to_string(i);
		const std::string start_open   = "start_open_" + std::to_string(i);
		const std::string finish_open  = "finish_open_" + std::to_string(i);
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
		const std::string i_s = std::to_string(i);
		const auto     far = i == 1 ? Location{"FAR"} : Location{"FAR_BEHIND_" + std::to_string(i - 1)};
		const Location near{"NEAR_" + i_s};
		const Location in{"IN_" + i_s};
		const Location behind{"BEHIND_" + i_s};
		const Location far_behind{"FAR_BEHIND_" + i_s};
		train_locations.insert({far, near, in, behind, far_behind});
		const std::string get_near{"get_near_" + i_s};
		const std::string enter{"enter_" + i_s};
		const std::string leave{"leave_" + i_s};
		const std::string travel{"travel_" + i_s};
		train_actions.insert({get_near, enter, leave, travel});
		train_transitions.push_back(
		  Transition{far,
		             get_near,
		             near,
		             {{"t", AtomicClockConstraintT<std::equal_to<Time>>(distances[i - 1])}},
		             {"t"}});
		train_transitions.push_back(
		  Transition{near,
		             enter,
		             in,
		             {{"t", AtomicClockConstraintT<std::greater_equal<Time>>(0)},
		              {"t", AtomicClockConstraintT<std::less_equal<Time>>(1)}},
		             {"t"}});
		train_transitions.push_back(Transition{
		  in, leave, behind, {{"t", AtomicClockConstraintT<std::equal_to<Time>>(1)}}, {"t"}});
		train_transitions.push_back(Transition{
		  behind, travel, far_behind, {{"t", AtomicClockConstraintT<std::equal_to<Time>>(2)}}, {"t"}});
		const auto finish_close_f = F{AP{finish_close}};
		const auto start_open_f   = F{AP{start_open}};
		const auto finish_open_f  = F{AP{finish_open}};
		const auto enter_f        = F{AP{enter}};
		const auto leave_f        = F{AP{leave}};
		const auto travel_f       = F{AP{travel}};
		spec_disjuncts.push_back(enter_f.dual_until(!finish_close_f)
		                         || start_open_f.dual_until(!leave_f)
		                         || travel_f.dual_until(!finish_open_f));
		std::cout<<"spec_disjuncts: "<<spec_disjuncts[i-1]<<std::endl;
	}
	automata.push_back(TA{train_locations,
	                      train_actions,
	                      Location{"FAR"},
	                      {Location{"FAR_BEHIND_" + std::to_string(distances.size())}},
	                      {"t"},
	                      train_transitions});
	environment_actions.insert(std::begin(train_actions), std::end(train_actions));
	auto spec = spec_disjuncts[0];
	std::for_each(std::next(std::begin(spec_disjuncts)),
	              std::end(spec_disjuncts),
	              [&spec](auto &&spec_disjunct) { spec = spec || spec_disjunct; });
	for (std::size_t i = 1; i < automata.size(); i++) {
		visualization::ta_to_graphviz(automata[i - 1])
		  .render_to_file(fmt::format("railroad{}_crossing_{}.pdf", distances.size(), i));
	}
	visualization::ta_to_graphviz(automata.back())
	  .render_to_file(fmt::format("railroad{}_train.pdf", distances.size()));


	// 生成图格式字符串
	//ta_to_graph_symmetry(automata::ta::get_product(automata));

	//tacos::automata::ta::TAToGraphConverter<LocationT, AP> converter(automata[0]);
	//converter.build_graph();
	//converter.print_graph(); 

    //Graph g = buildGraphFromTA(automata[0]);
	// auto [g,sub ]= tacos::automata::ta::buildGraphFromTA(automata::ta::get_product(automata));
	// tacos::automata::ta::TimedAutomaton<std::vector<std::string>, std::string> a =tacos::automata::ta::buildTAFromGraph(g);
	//TA a =tacos::automata::ta::buildTAFromGraph(g);
	//bool e = are_ta_equal(automata::ta::get_product(automata),a);
	//std::cout << "result" << e << std::endl;
	//Graph g = buildGraphFromTA(automata::ta::get_product(automata));	


	// 使用示例
	//*******auto* bliss_graph = convertToBlissDigraph(g);
	//******printBlissColors(bliss_graph, g);
	//****auto orbits = get_Orbits( bliss_graph );
	 // 用于存储搜索统计信
	// bliss::Stats stats;

	//  // 用于存储自同构生成器，每个生成器是一个排列（长度等于图的顶点数）
	// std::vector< std::vector<unsigned int> > generators;
 
	//  // 定义 report 回调函数，每发现一个生成器就保存一次
	// auto report = [&](unsigned int n, const unsigned int *aut) {
	// 	 // 将 aut 数组复制到一个 vector 中
	// 	std::vector<unsigned int> perm(aut, aut + n);
	// 	generators.push_back(perm);
	// };
 
	//  // 调用 find_automorphisms() 来计算图的自同构群
	// bliss_graph->find_automorphisms(stats, report);
 
	//  // 使用并查集计算轨道
	// unsigned int n = bliss_graph->get_nof_vertices();
	// std::vector<unsigned int> parent(n);
	// for (unsigned int i = 0; i < n; ++i) {
	// 	parent[i] = i;
	// }
 
	//  // 定义 find 函数（带路径压缩）
	//  std::function<unsigned int(unsigned int)> find = [&](unsigned int x) -> unsigned int {
	// 	 if (parent[x] != x) {
	// 		 parent[x] = find(parent[x]);
	// 	 }
	// 	 return parent[x];
	//  };
 
	//  // 定义 union 操作，将两个集合合并
	//  auto union_set = [&](unsigned int x, unsigned int y) {
	// 	 unsigned int rx = find(x);
	// 	 unsigned int ry = find(y);
	// 	 if (rx != ry) {
	// 		 parent[rx] = ry;
	// 	 }
	//  };
 
	//  // 对于每个生成器，将顶点 i 与其映射 perm[i] 合并到同一集合中
	//  for (const auto &perm : generators) {
	// 	 for (unsigned int i = 0; i < n; ++i) {
	// 		 union_set(i, perm[i]);
	// 	 }
	//  }
 
	//  // 收集轨道：对于每个顶点，找到其所在集合的代表
	// std::unordered_map<unsigned int, std::vector<unsigned int>> orbits;
	// for (unsigned int i = 0; i < n; ++i) {
	// 	unsigned int rep = find(i);
	// 	orbits[rep].push_back(i);
	// }
	// 输出所有轨道
	//*****printOrbits(orbits, g);
 
	
	//  // 清理内存
	// delete bliss_graph;

	
	// *****在主函数中添加以下代码（在计算轨道之后）
	//Graph merged_graph = mergeOrbitsInGraph(g, orbits);

	// 打印合并后的图
	// std::cout << "\nMerged Graph:\n";
	// for (const auto &node : merged_graph.getNodes()) {
	// 	std::cout << "NodeID=" << node.id << ", Type=" << static_cast<int>(node.type) << ", Label=\" ";
	// 	std::visit([](auto&& value) {
	// 		std::cout << value;
	// 	}, node.label);
	// 	std::cout << " \" "<<std::endl;
	// }

	//********这是合并轨道后的商自动机
	//tacos::automata::ta::TimedAutomaton<std::vector<std::string>, std::string> a_new =tacos::automata::ta::buildTAFromGraph(merged_graph);
	
	// std::cout << "\nMerged Edges:\n";
	// for (auto & [src, targets] : merged_graph.getAdjList()) {
	// 	for (auto dst : targets) {
	// 		std::cout << src << " --> " << dst << std::endl;
	// 	}
	// }


	
	// std::map<int, std::set<int>> simplified_adj_list;
	
	// // 创建轨道映射表：将原始节点映射到其轨道代表（这里用每个轨道中第一个节点作为代表）
	// std::map<int, int> node_to_orbit;
	// for (const auto &entry : orbits) {
	// 	int orbit_rep = entry.second[0]; // 选择轨道中的第一个节点作为代表
	// 	for (int node : entry.second) {
	// 		node_to_orbit[node] = orbit_rep;
	// 	}
	// }
	
	// // 合并边：如果两个节点属于同一轨道，则边合并为一条
	// for (const auto &[src, targets] : g2.getAdjList()) {
	// 	int orbit_src = node_to_orbit[src];
	// 	for (int dst : targets) {
	// 		int orbit_dst = node_to_orbit[dst];
	// 		simplified_adj_list[orbit_src].insert(orbit_dst);
	// 	}
	// }
	
	// // 为了确保孤立节点（没有边的）也被输出，构造所有轨道代表的集合
	// std::set<int> orbit_nodes;
	// for (const auto &p : node_to_orbit) {
	// 	orbit_nodes.insert(p.second);
	// }
	
	// // 输出简化后的节点及其 label
	// std::cout << "\nSimplified Nodes:" << std::endl;
	// for (int rep : orbit_nodes) {
	// 	// 在 g2.getNodes() 中查找 id 等于 rep 的节点
	// 	for (const auto &node : g2.getNodes()) {
	// 		if (node.id == rep) {
	// 			std::cout << "Node " << rep << " (Label: ";
	// 			std::visit([](auto&& value) {
	// 				std::cout << value;
	// 			}, node.label);
	// 			std::cout << ")" << std::endl;
	// 			break;
	// 		}
	// 	}
	// }
	
	// // 输出简化后的边
	// std::cout << "\nSimplified Edges:" << std::endl;
	// for (const auto &[src, targets] : simplified_adj_list) {
	// 	for (int dst : targets) {
	// 		std::cout << "Edge from " << src << " to " << dst << std::endl;
	// 	}
	// }
	// // 输出对比简化的图和原图的节点数
	// std::cout << "Total nodes: " << g2.getNodes().size() << std::endl;
	// std::cout << "Total Orbits: " << count << std::endl;


	
//打印原有向图节点数和生成的轨道数
	// std::cout<<"total nodes:"<<g2.getNodes().size()<<std::endl;
	// std::cout << "Total Orbits: " << count << std::endl;

	// std::map<int, std::set<int>> simplified_adj_list;


	// // 4) 打印分类结果
	// std::cout << "Classification: " << std::endl;
	// std::cout << result << std::endl;
	// std::vector<std::vector<int>> orbits = g.findSymmetry(g.getAdjList(), result);


	return std::make_tuple(automata::ta::get_product(automata),
	                       spec,
	                       controller_actions,
	                       environment_actions);
}
 