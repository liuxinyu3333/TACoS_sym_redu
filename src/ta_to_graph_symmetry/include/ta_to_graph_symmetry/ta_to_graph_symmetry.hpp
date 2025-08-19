#include "digraph.hh"
#include <unordered_map>
#include <set>
#include <sstream>      
#include <string> 

#include "graph_types.hpp"
#include "graph.hpp"
#include "ata_conversor.hpp"
#include "ta_conversor.hpp"
#include "automata/ata.h"
#include "automata/ata_formula.h"
#include "mtl/MTLFormula.h"
#include "automata/automata.h"
#include "automata/ta.h"
#include "automata/ta_product.h"
#include "automata/ta_regions.h"
#include "mtl/MTLFormula.h"






#include <cstdlib>

#include <algorithm>
#include <vector>
#include <map>
#include <set>
//#include <cstdlib>


using ta_class = tacos::automata::ta::TimedAutomaton<std::vector<std::string>, std::string>;
using ata_class = tacos::automata::ata::AlternatingTimedAutomaton<tacos::logic::MTLFormula<std::string>, tacos::logic::AtomicProposition<std::string>>;
using tran_typ = tacos::automata::ta::Transition<std::vector<std::string>, std::string>;
using loc_typ = tacos::automata::ta::Location<std::vector<std::string>>;
//using ata_form_typ = tacos::logic::MTLFormula<std::string>;


struct BlissResult {
    bliss::Digraph* graph;       // Bliss图对象
    unsigned dynamic_color;      // 动态颜色的最终值
};

template <typename LocationT, typename AP>
struct graph_orb{
    const Graph<LocationT, AP>& graph_original; // 原始图
    const Graph<LocationT, AP>& graph_simplified; // 简化图
    std::unordered_map< int, std::vector< int>> orbits; // 轨道映射
    std::unordered_map< int,  int> node_to_rep; // 节点到轨道代表的映射

    graph_orb(const Graph<LocationT, AP>& orig, Graph<LocationT, AP>& simpl)
      : graph_original(orig), graph_simplified(simpl)
    { }
};


struct result_automata{
    std::variant<std::shared_ptr<tacos::automata::ta::TimedAutomaton<std::vector<std::string>, std::string>>, 
                 std::shared_ptr<tacos::automata::ata::AlternatingTimedAutomaton<tacos::logic::MTLFormula<std::string>, tacos::logic::AtomicProposition<std::string>>>
                 > automata;
    std::unordered_map< int, std::vector< int>> orbits; // 轨道映射
    std::unordered_map< int,  int> node_to_rep; // 节点到轨道代表的映射
};



template <typename LocationT, typename AP>
BlissResult convertToBlissDigraph(const Graph<LocationT, AP>& graph) {
    // 基础颜色分配（确保每个 NodeType 都有唯一基础色）
    const std::unordered_map<NodeType, unsigned> base_colors = {
        {NodeType::TAInitialLocation,  0},  // 初始标记节点
        {NodeType::TAacceptLocation,   1},  // 接受标记节点
        {NodeType::TAResetClock,       2},
        {NodeType::TAClockGuard,       3},
        {NodeType::Location,           4},  // 普通 location 基础色
        {NodeType::Action,             5},
        {NodeType::TAClockVar,         6},
        {NodeType::TAComparisonOp,     7},  // 基础色（实际会被覆盖）
        {NodeType::TAConstant,         8}, // 基础色（实际会被覆盖）
        {NodeType::TAMiddleNode,       9},
        {NodeType::LocationFormula,   10},
        {NodeType::LogicOp,           11},
        {NodeType::formularoot,       12},
        {NodeType::LogicRoot,         13},
        {NodeType::SinkLocation,      14},
        {NodeType::ATAInitialLocation,15},
        {NodeType::ATAacceptLocation, 16},
        {NodeType::TrueFormula,       17},
        {NodeType::FalseFormula,      18},
        {NodeType::ATAResetClock,     19},
        {NodeType::ATAClockGuard,     20},
        {NodeType::ATAClockVar,       21},
        {NodeType::ATAMiddleNode,     22},
        {NodeType::ATAComparisonOp,   23},
        {NodeType::ATAConstant,       24},
        {NodeType::Controller_Action, 25},
        {NodeType::Environment_Action,26}
    
    };

    // 自定义特殊颜色：这些值可根据实际需要调整
    const unsigned INITIAL_LOCATION_COLOR = 27;  // 初始位置
    const unsigned ACCEPT_LOCATION_COLOR  = 28;  // 接受位置
    const unsigned NORMAL_LOCATION_COLOR  = 4;  // 普通位置
    const unsigned INITIAL_LOCATION_FORMULA_COLOR = 29;  // 初始位置
    const unsigned ACCEPT_LOCATION_FORMULA_COLOR  = 30;  // 接受位置
    const unsigned NORMAL_LOCATION_FORMULA_COLOR  = 10;  // 普通位置
    const unsigned CONTROLLER_ACTION_COLOR = 31; // 控制器动作
    const unsigned ENVIRONMENT_ACTION_COLOR = 32; // 环境动作

    // 预处理：收集由 Marker 节点指向的 Location 节点 
    std::set<int> TA_initial_locs, TA_accept_locs, ATA_initial_locs, ATA_accept_locs, ctr_act_middle, env_act_middle;
    
    // 1. 遍历所有节点，针对 Marker 类型（InitialLocation 和 AcceptLocation）
    //    收集其出边指向的类型为 Location 的节点
    for (const auto& node : graph.getNodes()) {
        if (node.type == NodeType::TAInitialLocation) {
            for (int target : graph.getAdjList().at(node.id)) {
                const auto& target_node = graph.getNodeWithID(target);
                if (target_node.type == NodeType::Location) {
                    TA_initial_locs.insert(target);
                }
            }
        }
        if (node.type == NodeType::TAacceptLocation) {
            for (int target : graph.getAdjList().at(node.id)) {
                const auto& target_node = graph.getNodeWithID(target);
                if (target_node.type == NodeType::Location) {
                    TA_accept_locs.insert(target);
                }
            }
        }
        if (node.type == NodeType::Controller_Action) {
            for (int target : graph.getAdjList().at(node.id)) {
                const auto& target_node = graph.getNodeWithID(target);
                if (target_node.type == NodeType::TAMiddleNode||target_node.type == NodeType::ATAMiddleNode) {
                    ctr_act_middle.insert(target);
                }
            }
        }
        if (node.type == NodeType::Environment_Action) {
            for (int target : graph.getAdjList().at(node.id)) {
                const auto& target_node = graph.getNodeWithID(target);
                if (target_node.type == NodeType::TAMiddleNode||target_node.type == NodeType::ATAMiddleNode) {
                    env_act_middle.insert(target);
                }
            }
        }

        if (node.type == NodeType::ATAInitialLocation) {
            for (int target : graph.getAdjList().at(node.id)) {
                const auto& target_node = graph.getNodeWithID(target);
                if (target_node.type == NodeType::LocationFormula) {
                    ATA_initial_locs.insert(target);
                }
            }
        }
        if (node.type == NodeType::ATAacceptLocation) {
            for (int target : graph.getAdjList().at(node.id)) {
                const auto& target_node = graph.getNodeWithID(target);
                if (target_node.type == NodeType::LocationFormula) {
                    ATA_accept_locs.insert(target);
                }
            }
        }
    }
    // 如果一个 Location 同时被两个 Marker 指向，则按初始位置处理
    for (auto id : TA_initial_locs) {
        TA_accept_locs.erase(id);
    }
    for (auto id : ATA_initial_locs) {
        ATA_accept_locs.erase(id);
    }

    // 2. 动态颜色生成器，用于比较操作符和常数的单独着色
    unsigned dynamic_color = 40; // 从基础颜色之后开始分配
    std::unordered_map<std::string, unsigned> TA_op_colors;   // 比较操作符颜色ta
    std::unordered_map<unsigned, unsigned> TA_const_colors;   // 常量颜色ta
    std::unordered_map<std::string, unsigned> ATA_op_colors;   // 比较操作符颜色ata
    std::unordered_map<unsigned, unsigned> ATA_const_colors;   // 常量颜色ata
    std::unordered_map<std::string, unsigned> Logic_Root_colors; //逻辑根节点颜色ata

    // 3. 创建 bliss 图
    bliss::Digraph* bliss_graph = new bliss::Digraph();
    // 使用 vector<unsigned int> 存储顶点ID（bliss 图中顶点由 add_vertex 返回 unsigned int）
    std::vector<unsigned int> vertices;
    vertices.resize(graph.getNodes().size());

    // 预创建所有顶点
    for (size_t i = 0; i < graph.getNodes().size(); ++i) {
        vertices[i] = bliss_graph->add_vertex();  // 返回顶点ID
    }
    
    // 4. 设置顶点颜色
    for (const auto& node : graph.getNodes()) {
        unsigned color = 0;
        switch (node.type) {
            // Marker 节点直接使用基础颜色
            case NodeType::TAacceptLocation:
                color = base_colors.at(node.type);
                break;
            // Location 节点根据 Marker 指向情况着色
            case NodeType::Location: {
                if (TA_initial_locs.count(node.id)) {
                    color = INITIAL_LOCATION_COLOR;
                } else if (TA_accept_locs.count(node.id)) {
                    color = ACCEPT_LOCATION_COLOR;
                } else {
                    color = NORMAL_LOCATION_COLOR;
                }
                break;
            }
            case NodeType::LocationFormula: {
                if (ATA_initial_locs.count(node.id)) {
                    color = INITIAL_LOCATION_FORMULA_COLOR;
                } else if (ATA_accept_locs.count(node.id)) {
                    color = ACCEPT_LOCATION_FORMULA_COLOR;
                } else {
                    color = NORMAL_LOCATION_FORMULA_COLOR;
                }
                break;
            }
            // 对于 ComparisonOp 类型，根据具体操作符单独着色
            case NodeType::TAComparisonOp: {
                const auto& op = std::get<ComparisonOpLabel>(node.label).get();
                if (!TA_op_colors.count(op)) {
                    TA_op_colors[op] = dynamic_color++;
                }
                color = TA_op_colors[op];
                break;
            }
            // 对于 LogicRoot 类型，根据逻辑根字符串单独着色
            case NodeType::LogicRoot:{
                const auto& op = std::get<MarkerLabel>(node.label).get();
                if (!Logic_Root_colors.count(op)) {
                    Logic_Root_colors[op] = dynamic_color++;
                }
                color = Logic_Root_colors[op];
                break;
            }
            // 对于 Constant 类型，根据常数值单独着色
            case NodeType::TAConstant: {
                unsigned value = std::get<ConstantLabel>(node.label);
                if (!TA_const_colors.count(value)) {
                    TA_const_colors[value] = dynamic_color++;
                }
                color = TA_const_colors[value];
                break;
            }
            case NodeType::ATAComparisonOp:{
                const auto& op = std::get<ComparisonOpLabel>(node.label).get();
                if (!ATA_op_colors.count(op)) {
                    ATA_op_colors[op] = dynamic_color++;
                }
                color = ATA_op_colors[op];
                break;
            }
            case NodeType::ATAConstant:{
                unsigned value = std::get<ConstantLabel>(node.label);
                if (!ATA_const_colors.count(value)) {
                    ATA_const_colors[value] = dynamic_color++;
                }
                color = ATA_const_colors[value];
                break;
            }
            case NodeType::ATAMiddleNode:{
                if (ctr_act_middle.count(node.id)) {
                    color = CONTROLLER_ACTION_COLOR;
                } else if (env_act_middle.count(node.id)) {
                    color = ENVIRONMENT_ACTION_COLOR;
                } else {
                    color = base_colors.at(node.type);
                }
                break;
            }
            case NodeType::TAMiddleNode:{
                if (ctr_act_middle.count(node.id)) {
                    color = CONTROLLER_ACTION_COLOR;
                } else if (env_act_middle.count(node.id)) {
                    color = ENVIRONMENT_ACTION_COLOR;
                } else {
                    color = base_colors.at(node.type);
                }
                break;
            }
            // 其它类型使用预设的基础颜色
            default:
                color = base_colors.at(node.type);
        }
        // 设置顶点颜色，vertices[node.id] 为 bliss 图中的顶点ID
       // node.color = color; // 更新原图节点的颜色
        //std::cout << "Node:" << node.id << " , type: " << static_cast<int>(node.type) << " , color: " << color <<std::endl;

        bliss_graph->change_color(vertices[node.id], color);
    }

    // 5. 添加边
    for (const auto& [src, targets] : graph.getAdjList()) {
        for (int tgt : targets) {
            bliss_graph->add_edge(src, tgt);
            //std::cout << "Add edge: " << src << " -> " << tgt << std::endl;
        }
    }
    
    // 如果代码中有处理 orbit 字符串的部分，也需要确保使用 std::istringstream/std::ostringstream，
    // 并包含 <sstream> 以及 <string>，这样 getline 和 >> 操作符就可以正常使用。

    return {bliss_graph, dynamic_color};
}

std::pair<
    std::unordered_map< int, std::vector< int>>, 
    std::unordered_map< int,  int>
>
get_Orbits(bliss::Digraph* bliss_graph){

    	 // 用于存储搜索统计信息
	bliss::Stats stats;

    // 用于存储自同构生成器，每个生成器是一个排列（长度等于图的顶点数）
   std::vector< std::vector<unsigned int> > generators;

    // 定义 report 回调函数，每发现一个生成器就保存一次
   auto report = [&](unsigned int n, const unsigned int *aut) {
        // 将 aut 数组复制到一个 vector 中
       std::vector<unsigned int> perm(aut, aut + n);
       generators.push_back(perm);
   };

    // 调用 find_automorphisms() 来计算图的自同构群
   bliss_graph->find_automorphisms(stats, report);

    // 使用并查集计算轨道
   unsigned int n = bliss_graph->get_nof_vertices();
   std::vector<unsigned int> parent(n);
   for (unsigned int i = 0; i < n; ++i) {
       parent[i] = i;
   }

    // 定义 find 函数（带路径压缩）
    std::function<unsigned int(unsigned int)> find = [&](unsigned int x) -> unsigned int {
        if (parent[x] != x) {
            parent[x] = find(parent[x]);
        }
        return parent[x];
    };

    // 定义 union 操作，将两个集合合并
    auto union_set = [&](unsigned int x, unsigned int y) {
        unsigned int rx = find(x);
        unsigned int ry = find(y);
        if (rx != ry) {
            parent[rx] = ry;
        }
    };

    // 对于每个生成器，将顶点 i 与其映射 perm[i] 合并到同一集合中
    for (const auto &perm : generators) {
        for (unsigned int i = 0; i < n; ++i) {
            union_set(i, perm[i]);
        }
    }

    // 收集轨道：对于每个顶点，找到其所在集合的代表
    std::unordered_map<int, int> node_to_rep;
    std::unordered_map<int, std::vector<int>> orbits;
    for (unsigned int i = 0; i < n; ++i) {
        unsigned int rep = find(i);
        orbits[static_cast<int>(rep)].push_back(static_cast<int>(i));
        node_to_rep[static_cast<int>(i)] = static_cast<int>(rep);
    }
    return {orbits, node_to_rep};
}


      
template <typename LocationT, typename AP>
std::tuple<Graph<LocationT, AP>, std::unordered_map< int,  int>> mergeOrbitsInGraph(
    const Graph<LocationT, AP>& originalGraph,
    const std::unordered_map< int, std::vector< int>>& orbits) {
    
    // 1. 构造从原图每个节点到其所在轨道代表的映射
    std::unordered_map< int,  int> nodeToOrbitRep;
    
    // 2. 在新图中为每个轨道添加一个合并节点
    Graph<LocationT, AP> simplifiedGraph;
    // 保存轨道代表到新图节点 id 的映射
    std::unordered_map< int,  int> orbitRepToNewNode;
    std::map<std::set<std::string>, std::string> LabelsToRep;
   // std::set<std::string> labels;
    for (const auto& orbitPair : orbits) {
        int rep = orbitPair.first;
        // 取原图中代表节点的信息
        auto origNode = originalGraph.getNodeWithID(rep);
        
        for ( int nodeId : orbitPair.second) {
            nodeToOrbitRep[nodeId] = rep;

            
        }
        //std::cout<<""<<std::endl;
        //std::cout<<"org Node:" << rep << " , type: " << static_cast<int>(origNode.type) << " , label: " << ori_label <<std::endl;

        // 在新图中添加节点（标签和类型保持不变）
         int newNodeId = simplifiedGraph.addNode(origNode.label, origNode.type);
        orbitRepToNewNode[rep] = newNodeId;
    }
    
    // 3. 遍历原图所有边，将边映射到合并后的节点上
    const auto& adjList = originalGraph.getAdjList();
    //auto& adj_sim = simplifiedGraph.getAdjList();

    for (const auto& kv : adjList) {
         int src = kv.first;
        for (int tgt : kv.second) {
            int repSrc = nodeToOrbitRep[src];
            int repTgt = nodeToOrbitRep[tgt];
            // 如果两个端点来自不同的轨道，则在简化图中添加对应的边
            if (repSrc != repTgt) {

                int newSrc = orbitRepToNewNode[repSrc];
                int newTgt = orbitRepToNewNode[repTgt];
                if (std::find(simplifiedGraph.getAdjList().at(newSrc).begin(), simplifiedGraph.getAdjList().at(newSrc).end(), newTgt) == simplifiedGraph.getAdjList().at(newSrc).end()){
                    simplifiedGraph.addEdge(newSrc, newTgt);
                }
            }
        }
    }



    std::cout << "Merged graph has " << simplifiedGraph.getNodes().size() << " nodes and " 
              << simplifiedGraph.getAdjList().size() << " edges." << std::endl;
    return std::make_tuple(simplifiedGraph, orbitRepToNewNode);
}



// 打印所有节点颜色信息
template <typename LocationT, typename AP>
void printBlissColors(const bliss::Digraph* g, const Graph<LocationT, AP>& orig) {
    for (size_t i = 0; i < g->get_nof_vertices(); ++i) {
        const auto& node = orig.getNodeWithID(i);
        std::cout << "Node " << i 
                  << " [Type: " << static_cast<int>(node.type)
                  << "] Color: " << g->get_color(i) << "\n";
    }
}


bool compare_infos(const std::unordered_map< int, std::vector< int>>& map1, const std::unordered_map< int, std::vector< int>>& map2){
    for (const auto& [key, vec1] : map1) {
        auto it = map2.find(key);
        if (it == map2.end()) {
            std::cout << "[MISSING] Key " << key << " only in first map" << std::endl;
            return false;
        }

        const auto& vec2 = it->second;
        if (vec1 != vec2) {
            std::cout << "[CONTENT DIFF] Key " << key 
                      << " vectors differ (size: " 
                      << vec1.size() << " vs " << vec2.size() << ")" << std::endl;
            return false;
        }
    }

    // 阶段二：反向查漏
    for (const auto& [key, vec2] : map2) {
        if (map1.find(key) == map1.end()) {
            std::cout << "[MISSING] Key " << key << " only in second map" << std::endl;
            return false;
        }
    }

    if (map1.size() != map2.size()) {
        std::cout << "[SIZE DIFF] Map sizes differ (map1: " 
                  << map1.size() << ", map2: " << map2.size() << ")" << std::endl;
        return false;
    }
    return true;
}


template <typename LocationT, typename AP>
auto compute_transition_orbits(
    const std::unordered_map< int,  int>& node_to_orbit_rep,
    const std::map<tacos::automata::ta::Transition<LocationT, AP>, tacos::automata::ta::TransitionSubgraphInfo>& transition_info)
{
    // Step 1: 构造节点到轨道代表的映射（如材料3）
    // struct TransOrbit {
    //     automata::ta::Transition<LocationT, AP> rep_trans;
    //     std::vector<automata::ta::Transition<LocationT, AP>> member_trans;
    // };
    // Step 2: 遍历所有transition信息（材料4）
    //std::map<tacos::automata::ta::Transition<LocationT, AP>, TransitionSubgraphInfo> transitionSubgraphs;
    std::vector<tacos::automata::ta::Transition<LocationT, AP>> transition;
    transition.reserve(transition_info.size());
    for (const auto& [trans, info] : transition_info) {
        transition.push_back(trans);
    }
    std::map<tacos::automata::ta::Transition<LocationT, AP>, std::vector<tacos::automata::ta::Transition<LocationT, AP>>> transition_orbits;
    std::vector<bool> visited(transition_info.size(), false);
    for (std::size_t i=0; i<transition.size(); ++i){
        if (visited[i]){
            continue;
        }
        visited[i] = true;
        transition_orbits[transition[i]].push_back(transition[i]);
        std::cout << "Transition: " << transition[i] << std::endl;
        auto tran_1 = transition_info.at(transition[i]);
        auto tran_1_src_rep = node_to_orbit_rep.at(tran_1.source);
        auto tran_1_tgt_rep = node_to_orbit_rep.at(tran_1.target);
        auto tran_1_action_rep = node_to_orbit_rep.at(tran_1.action); // 需实现动作轨道分析
        auto tran_1_middle_rep = node_to_orbit_rep.at(tran_1.middle);
        //transform clockconstranits to orbit representative
        std::unordered_map< int, std::vector< int>> tran_1_clock_guards_rep;
        for (const auto& [guard, constraints] : tran_1.clock_guards) {
            std::vector< int> constraints_rep;
            for ( int item : constraints) {
                constraints_rep.push_back(node_to_orbit_rep.at(item));
            }
            tran_1_clock_guards_rep[node_to_orbit_rep.at(guard)] = constraints_rep;
        }
        std::unordered_map< int, std::vector< int>> tran_1_clock_reset_rep;
        for (const auto& [reset, clocks] : tran_1.reset) {
            std::vector< int> clocks_rep;
            for ( int item : clocks) {
                clocks_rep.push_back(node_to_orbit_rep.at(item));
            }
            tran_1_clock_reset_rep[node_to_orbit_rep.at(reset)] = clocks_rep;
        }

        for (std::size_t j=i+1; j<transition.size();++j){
            if (visited[j]){
                continue;
            }
            auto tran_2 = transition_info.at(transition[j]);
            // 计算两个transition的轨道代表
            if ((tran_1_src_rep==node_to_orbit_rep.at(tran_2.source))&&
                (tran_1_tgt_rep==node_to_orbit_rep.at(tran_2.target))&&
                (tran_1_action_rep==node_to_orbit_rep.at(tran_2.action))&&
                (tran_1_middle_rep==node_to_orbit_rep.at(tran_2.middle))) {

                    std::unordered_map< int, std::vector< int>> tran_2_clock_guards_rep;
                    for (const auto& [guard, constraints] : tran_2.clock_guards) {
                        std::vector< int> constraints_rep;
                        for ( int item : constraints) {
                            constraints_rep.push_back(node_to_orbit_rep.at(item));
                        }
                        tran_2_clock_guards_rep[node_to_orbit_rep.at(guard)] = constraints_rep;
                    }

                    std::unordered_map< int, std::vector< int>> tran_2_clock_reset_rep;
                    for (const auto& [reset, clocks] : tran_2.reset) {
                        std::vector< int> clocks_rep;
                        for ( int item : clocks) {
                            clocks_rep.push_back(node_to_orbit_rep.at(item));
                        }
                        tran_2_clock_reset_rep[node_to_orbit_rep.at(reset)] = clocks_rep;
                    }

                    if (compare_infos(tran_1_clock_guards_rep, tran_2_clock_guards_rep)&&
                        compare_infos(tran_1_clock_reset_rep, tran_2_clock_reset_rep)){
                            // 如果两个transition的轨道代表相同，则将它们添加到同一轨道中 
                            transition_orbits[transition[i]].push_back(transition[j]);
                            
                            visited[j] = true;
                        }

                }
            
        }
    }
    

    return transition_orbits;
}


std::tuple< result_automata, result_automata, std::map<std::string, tacos::logic::AtomicProposition<std::string>>>
get_action_Orbits_map(const ta_class& ta, const ata_class& ata, const std::set<std::string> &controller_actions ){


    using symbol_t =  tacos::logic::AtomicProposition<std::string>;
    using ata_loc = tacos::logic::MTLFormula<std::string>;
    //using formula_t = tacos::automata::ata::Formula<ata_loc>;
    using Transition_t = tacos::automata::ata::Transition<ata_loc, symbol_t>;

	auto ata_graph = tacos::automata::ata::buildGraphFromATA(ata, controller_actions);	
	auto [ta_graph, taTrans_to_subgraph ]= tacos::automata::ta::buildGraphFromTA(ta, controller_actions);
    auto ta_bliss_result = convertToBlissDigraph(ta_graph);
    auto ata_bliss_result = convertToBlissDigraph(ata_graph);

    auto ta_bliss_graph = ta_bliss_result.graph;
    auto ata_bliss_graph = ata_bliss_result.graph;
   // std::cout<<"ta_bliss_graph: "<<ta_bliss_graph->get_nof_vertices()<<std::endl;

    auto ta_dynamic_color = ta_bliss_result.dynamic_color;
    //auto ata_dynamic_color = ata_bliss_result.dynamic_color;
    
    auto [orbits_ta, ta_nodes_to_rep] = get_Orbits(ta_bliss_graph); 
    auto [orbits_ata, ata_nodes_to_rep] = get_Orbits(ata_bliss_graph);
    std::vector<std::vector< int>> action_ta;
    std::vector<std::vector< int>> action_ata;
    std::vector<std::vector< int>> result_action_ta;
   


    for (const auto &TAorbit : orbits_ta){//获取到ta的轨道的集合
        auto TArep = ta_graph.getNodeWithID(TAorbit.first);
        if (TArep.type  == NodeType::Controller_Action ||
            TArep.type == NodeType::Environment_Action){
            
            action_ta.push_back(TAorbit.second);
            
        }
    }

    for (const auto &ATAorbit : orbits_ata){//获取到ata的轨道的集合
        auto ATArep = ata_graph.getNodeWithID(ATAorbit.first);
        if (ATArep.type  == NodeType::Controller_Action ||
            ATArep.type == NodeType::Environment_Action){
            action_ata.push_back(ATAorbit.second);
        }
    }
    
    //std::cout << "TA action: "  << " color: " << ta_bliss_result.graph->get_nof_vertices()<< std::endl;

    for (auto TA_actions : action_ta){
        for (auto ATA_actions : action_ata){
            std::vector< int> split_TA_action;
            for (const auto TA_action_id : TA_actions){
                auto TA_action = std::get<std::string>(ta_graph.getNodeWithID(TA_action_id).label);
                for(const auto ATA_action_id : ATA_actions){
                    auto ATA_action = std::get<tacos::logic::AtomicProposition<std::string>>(ata_graph.getNodeWithID(ATA_action_id).label);
                    if (tacos::automata::ata::formula_to_string(TA_action) == tacos::automata::ata::formula_to_string(ATA_action)){
                        split_TA_action.push_back(TA_action_id);
                    }
                }
            }
            if (split_TA_action.size() > 0){
                result_action_ta.push_back(split_TA_action);
            }

        }
    }
   
    for (auto TA_actions : result_action_ta){

        ++ta_dynamic_color;
        for (auto action : TA_actions){
           // std::cout << "TA action: " << action << " color: " << ta_bliss_result.graph->get_color(static_cast<size_t>(action)) << std::endl;
            ta_bliss_graph->change_color(action, ta_dynamic_color);
           // std::cout << "TA action: " << action <<" "<< tacos::automata::ata::formula_to_string(ta_graph.getNodeWithID(action).label)<< " color: " << ta_dynamic_color << std::endl;
           //std::cout << "TA action: " << action << " color: " << ta_bliss_result.graph->get_color(static_cast<size_t>(action)) << std::endl;
        }
    }
   
   
    if (!ta_bliss_graph || !ata_bliss_graph) {
        throw std::runtime_error("Failed to convert graph to Bliss digraph");
    }

    auto [orbits_ta_new, ta_nodes_to_rep_new] = get_Orbits(ta_bliss_graph); //获取新的ta轨道（如果ta和ata的action有交叉）

    std::map<std::string, tacos::logic::AtomicProposition<std::string>> action_map;

    for (const auto &TAorbit : orbits_ta_new){//获取到ta的轨道的集合
        auto TArep = ta_graph.getNodeWithID(TAorbit.first);

        if (TArep.type == NodeType::Controller_Action ||
            TArep.type == NodeType::Environment_Action){
            for (const auto &ATAorbit : orbits_ata){
                auto ATArep = ata_graph.getNodeWithID(ATAorbit.first);
                //std::cout << "ATA action: " << tacos::automata::ata::formula_to_string(ATArep.label) << std::endl;
                if (ATArep.type == NodeType::Controller_Action ||
                    ATArep.type == NodeType::Environment_Action){
                    for (const auto ATA_action_id : ATAorbit.second){
                        auto ATA_action = std::get<tacos::logic::AtomicProposition<std::string>>(ata_graph.getNodeWithID(ATA_action_id).label);
                        if (tacos::automata::ata::formula_to_string(std::get<std::string>(TArep.label)) == tacos::automata::ata::formula_to_string(ATA_action)){
                            //std::cout<< tacos::automata::ata::formula_to_string(std::get<std::string>(TArep.label)) << " == " << tacos::automata::ata::formula_to_string(ATA_action) << std::endl;
                            if (action_map.find(std::get<std::string>(TArep.label)) == action_map.end()){
                                auto ATA_action_r = std::get<tacos::logic::AtomicProposition<std::string>>(ata_graph.getNodeWithID(ata_nodes_to_rep[ATA_action_id]).label);
                                //action_map[std::get<std::string>(TArep.label)] = std::get<tacos::logic::AtomicProposition<std::string>>(ATArep.label);
                               // std::cout << "ATA action rep: " << tacos::automata::ata::formula_to_string(std::get<tacos::logic::AtomicProposition<std::string>>(ata_graph.getNodeWithID(ATAorbit.first).label)) << std::endl;


                                action_map.insert({ std::get<std::string>(TArep.label), ATA_action_r });
                            }else{
                                std::cout << "Error: action map has duplicate keys" << std::endl;
                            }
                            
                        }
                    }
                    //std::cout << "ATA action: " << std::get<tacos::logic::AtomicProposition<std::string>>(ata_graph.getNodeWithID(ATAorbit.first).label) << std::endl;
                }
                
            }
        }

        
    }

    auto taR = mergeOrbitsInGraph(ta_graph, orbits_ta_new);
    auto graph_ta_orb = std::get<0>(taR);
    auto rep_to_sim_ta = std::get<1>(taR);
    auto ataR = mergeOrbitsInGraph(ata_graph, orbits_ata);
    auto graph_ata_orb = std::get<0>(ataR);
    auto rep_to_sim_ata = std::get<1>(ataR);




    auto graph_ta_orb_nodes = graph_ta_orb.getNodes();
	auto graph_ta_orb_adj = graph_ta_orb.getAdjList();
	for (auto& node : graph_ta_orb_nodes){
		if (node.type == NodeType::Controller_Action ||
            node.type == NodeType::Environment_Action){
			for (auto& v : graph_ta_orb_adj[node.id]){
                    graph_ta_orb.changeLabel(v, node.label);
			}
		}
	} 
    //graph_ta_orb.exportDOT("graph_ta_orb.dot");
    auto graph_ata_orb_nodes = graph_ata_orb.getNodes();
    auto graph_ata_orb_adj = graph_ata_orb.getAdjList();
    for (auto& node : graph_ata_orb_nodes){
        if (node.type == NodeType::Controller_Action ||
            node.type == NodeType::Environment_Action){
            for (auto& v : graph_ata_orb_adj[node.id]){
                graph_ata_orb.changeLabel(v, node.label);
            }
        }
    }
   
    auto ta_ptr_and_map = tacos::automata::ta::buildTAFromGraph(graph_ta_orb);
    auto ta_ptr = std::get<0>(ta_ptr_and_map);
    //auto ta_trans_to_transinfo = std::get<1>(ta_ptr_and_map);
    //std::cout << "sim ta has " << ta_ptr->get_transitions().size()<<" trans." << std::endl;
    
    //std::cout << "ATA org:  " << ata << std::endl;
    
    auto ata_ptr = tacos::automata::ata::buildATAFromGraph(graph_ata_orb);

    auto re_ata_alphabet = ata_ptr->get_alphabet();
    //std::cout << "sim ata has " << re_ata_alphabet.size();
    //auto re_ata_transitions = ata_ptr->get_transitions();
    //std::cout << "sim ata has " << re_ata_transitions.size();
    auto re_ata_sink = ata_ptr->get_sink_location();
    auto re_ata_final_loc = ata_ptr->get_final_locations();
    auto re_ata_initial_loc = ata_ptr->get_initial_location();



    std::vector<Transition_t> transitions_re;
    std::vector<bool> visited(ata_ptr->get_transitions().size(), false);


    // 假设 re_ata_transitions 是 std::set<Transition<Loc,Sym>>
    int i = 0;
    for (auto it1 = ata_ptr->get_transitions().begin(); it1 != ata_ptr->get_transitions().end(); ++it1) {
        std::vector<Transition_t> disjunct;
        if (!visited[i]){
            
            
            auto ptr_form1 = it1->get_uni_Formula();
            
            for (auto it2 = std::next(it1); it2 != ata_ptr->get_transitions().end(); ++it2) {
                auto ptr_form2 = it2->get_uni_Formula();
                
                int j = i+1;
                if (!visited[j]){

                    
                    if (tacos::automata::ata::formula_to_string(it1->symbol_) == tacos::automata::ata::formula_to_string(it2->symbol_) &&
                        tacos::automata::ata::formula_to_string(*ptr_form1) != tacos::automata::ata::formula_to_string(*ptr_form2) && 
                        tacos::automata::ata::formula_to_string(it1 ->source_) == tacos::automata::ata::formula_to_string(it2->source_)){
                        //std::cout<<*ptr_form2 << std::endl;
                        //auto formula = tacos::automata::ata::create_disjunction<ata_loc>(std::move(ptr_form1), std::move(ptr_form2));
                        disjunct.emplace_back(it2 ->source_, it2->symbol_, std::move(ptr_form2));
                //disjunct.emplace_back(it1 ->source_, it1->symbol_, std::move(ptr_form2));
                        visited[j] = true;
                        
              
                    }
                    
                }
                j++;
            }
            //std::cout << "disjunct size: " << disjunct.size() << std::endl;
            if (disjunct.size() > 0){

                auto t0 = std::move(disjunct[0]);
                auto form0 = t0.get_uni_Formula();
                std::cout<<"form0:" << *form0 << std::endl;
                auto formula = tacos::automata::ata::create_disjunction<ata_loc>(std::move(ptr_form1), std::move(form0));

                for (size_t k = 1; k < disjunct.size(); ++k) {
                    auto f_k = std::move(disjunct[k]);
                    auto form_k = f_k.get_uni_Formula();
                    formula = tacos::automata::ata::create_disjunction<ata_loc>(std::move(formula), std::move(form_k));
                    
                    
                }
                std::cout <<"formula:" << *formula << std::endl;
                transitions_re.emplace_back(it1->source_, it1->symbol_, std::move(formula));

                
            }else{
                transitions_re.emplace_back(it1->source_, it1->symbol_, std::move(ptr_form1));
            }
            visited[i] = true;
        }
        i++;
        
    }

    
        
    
    

    auto re_ata_ptr = std::make_shared<tacos::automata::ata::AlternatingTimedAutomaton<ata_loc, symbol_t>>(
        re_ata_alphabet,
        re_ata_initial_loc,
        re_ata_final_loc,
        //std::move(re_ata_transitions),
        tacos::automata::ata::vectorToSet(std::move(transitions_re)),
        re_ata_sink
    );

    //std::cout << "sim ata has " << ata_result->get_transitions().size()<<" trans." << std::endl;
    //auto ata_g = tacos::automata::ata::buildATAFromGraph(ata_graph);
    
    
    
    
    //std::cout << "TA sim:  " << *ta_ptr << std::endl;
    result_automata result_ta = {ta_ptr,orbits_ta_new, ta_nodes_to_rep_new};
    result_automata result_ata = {re_ata_ptr,orbits_ata, ata_nodes_to_rep};


    return std::make_tuple(result_ta, result_ata, action_map);
    

}




template <typename LocationT1, typename AP1, typename LocationT2, typename AP2>
std::tuple<
    Graph<LocationT1, std::string>,
    std::unordered_map< int,  int>,
    std::unordered_map< int,  int>,
    std::unordered_map< int,  int>,
    std::unordered_map< int,  int>,
    std::unordered_map< int,  int>,
    std::unordered_map< int,  int>
> mergeGraphs(
    const Graph<LocationT1, AP1>& ta_graph,
    const Graph<LocationT2, AP2>& ata_graph) {
    
    Graph<LocationT1, std::string> merged_graph;
    std::unordered_map<std::string,  int> action_label_to_node;
    std::unordered_map< int, int> ta_to_merged;
    std::unordered_map< int, int> merged_to_ta;
    std::unordered_map< int, int> merged_to_ta_action;

    std::unordered_map< int, int> ata_to_merged;
    std::unordered_map< int, int> merged_to_ata;
    std::unordered_map< int, int> merged_to_ata_action;

    //int count_ata = 0;
    // 合并 TA 图中的节点
    for (const auto& node : ta_graph.getNodes()) {
        if (node.type == NodeType::Controller_Action ||
            node.type == NodeType::Environment_Action) {
            std::string label = tacos::automata::ata::formula_to_string(std::get<AP1>(node.label));
            if (action_label_to_node.find(label) == action_label_to_node.end()) {
                int new_node_id = merged_graph.addNode(label, node.type);
                action_label_to_node[label] = new_node_id;
            }
            ta_to_merged[node.id] = action_label_to_node[label];
            merged_to_ta_action[action_label_to_node[label]] = node.id;
            
            
        } else if(node.type == NodeType::TAComparisonOp){
              // 对于 ComparisonOp 类型，根据具体操作符单独着色
              
            const auto& label = std::get<ComparisonOpLabel>(node.label).get();
            int new_node_id = merged_graph.addNode(ComparisonOpLabel(label), node.type);
            ta_to_merged[node.id] = new_node_id;
            merged_to_ta[new_node_id] = node.id;
        }else if(node.type == NodeType::TAConstant){
            
            unsigned value = std::get<ConstantLabel>(node.label);
            int new_node_id = merged_graph.addNode(ConstantLabel(value), node.type);
            ta_to_merged[node.id] = new_node_id;
            merged_to_ta[new_node_id] = node.id;

        }else{
            int new_node_id = merged_graph.addNode(" ", node.type);
            ta_to_merged[node.id] = new_node_id;
            merged_to_ta[new_node_id] = node.id;
        }
    }

    // 合并 TA 图中的边
    for (const auto& [src, targets] : ta_graph.getAdjList()) {
        for ( int tgt : targets) {
            int new_src = ta_to_merged[src];
            int new_tgt = ta_to_merged[tgt];
            merged_graph.addEdge(new_src, new_tgt);
        }
    }

    // 合并 ATA 图中的节点
    for (const auto& node : ata_graph.getNodes()) {
        if (node.type == NodeType::Controller_Action ||
            node.type == NodeType::Environment_Action) {
            std::string label = tacos::automata::ata::formula_to_string(std::get<AP2>(node.label));
            if (action_label_to_node.find(label) == action_label_to_node.end()) {
                int new_node_id = merged_graph.addNode(label, node.type);
                action_label_to_node[label] = new_node_id;
            }
            ata_to_merged[node.id] = action_label_to_node[label];
            merged_to_ata_action[action_label_to_node[label]] = node.id;
        }else if(node.type == NodeType::ATAComparisonOp){

            const auto& label = std::get<ComparisonOpLabel>(node.label).get();
            int new_node_id = merged_graph.addNode(ComparisonOpLabel(label), node.type);
            ata_to_merged[node.id] = new_node_id;
            merged_to_ata[new_node_id] = node.id;

        }else if(node.type == NodeType::ATAConstant){

            unsigned value = std::get<ConstantLabel>(node.label);
     
            int new_node_id = merged_graph.addNode(ConstantLabel(value), node.type);
            ata_to_merged[node.id] = new_node_id;
            merged_to_ata[new_node_id] = node.id;

        }else if(node.type == NodeType::LogicRoot){
            const auto& label = std::get<MarkerLabel>(node.label).get();
       
            int new_node_id = merged_graph.addNode(MarkerLabel(label), node.type);
            ata_to_merged[node.id] = new_node_id;
            merged_to_ata[new_node_id] = node.id;

        } else {
            int new_node_id = merged_graph.addNode(" ", node.type);
            ata_to_merged[node.id] = new_node_id;
            merged_to_ata[new_node_id] = node.id;
        }
    }

    // 合并 ATA 图中的边
    for (const auto& [src, targets] : ata_graph.getAdjList()) {
        for ( int tgt : targets) {
            int new_src = ata_to_merged[src];
            int new_tgt = ata_to_merged[tgt];
            merged_graph.addEdge(new_src, new_tgt);
        }
    }
    auto re_adj = merged_graph.getAdjList();
    for (const auto& node : merged_graph.getNodes()) {
        if (node.type == NodeType::ATAInitialLocation) {
            auto it = re_adj.find(node.id);
            if (it != re_adj.end()) {
                for (const auto& v : it->second) {
                    auto see = merged_to_ata.at(v);
                    auto see_node = ata_graph.getNodeWithID(see);
                    std::cout << " successor: " << see_node.id << " , type :" << static_cast<int>( see_node.type) << " , label : " <<std::endl;//<< tacos::automata::ata::formula_to_string(std::get<std::string>(see_node.label))<< std::endl;
                    const auto& succ = merged_graph.getNodeWithID(v);
                    std::cout << " merge successor: " << succ.id << " , type :" << static_cast<int>(succ.type) << " , label : " << tacos::automata::ata::formula_to_string(std::get<std::string>(succ.label))<< std::endl;
     
                }
            }
        }
    }


    return std::make_tuple(merged_graph, ta_to_merged, ata_to_merged, merged_to_ta, merged_to_ata, merged_to_ta_action, merged_to_ata_action);
}


std::tuple< std::shared_ptr<ta_class>, std::shared_ptr<ata_class>, std::map<loc_typ, std::vector<loc_typ>>, std::map<tran_typ, std::vector<tran_typ>> >
get_symmetry_result(const ta_class& ta, const ata_class& ata, const std::set<std::string> &controller_actions ){

	auto ata_graph = tacos::automata::ata::buildGraphFromATA(ata, controller_actions);	
	auto [ta_graph, taTrans_to_subgraph ]= tacos::automata::ta::buildGraphFromTA(ta, controller_actions);
    


	auto [g_merge, ta_to_merged, ata_to_merged, merged_to_ta, merged_to_ata, merged_to_ta_action, merged_to_ata_action] = mergeGraphs(ta_graph, ata_graph);

    auto merge_bliss_result = convertToBlissDigraph(g_merge);
    auto merge_bliss_graph = merge_bliss_result.graph;

    auto [orbits_merge, nodes_to_rep] = get_Orbits(merge_bliss_graph);

    std::cout<< "Merged graph has " << merge_bliss_graph->get_nof_vertices() << " nodes and " << std::endl;

    std::cout<<"orbits size: " << orbits_merge.size() << std::endl;


    std::unordered_map< int, std::vector< int>> ta_orbits;
    std::unordered_map< int, std::vector< int>> ata_orbits;
    std::unordered_map< int,  int> ta_nodes_to_rep;
    std::unordered_map< int,  int> ata_nodes_to_rep;

    for (const auto &merge_orbit : orbits_merge){//将ta与ata合并图的轨道分开映射回到原来的ta和ata中
        if (merged_to_ta.find(merge_orbit.first) != merged_to_ta.end()){
            auto ta_rep_id = merged_to_ta.at(merge_orbit.first);
            std::vector< int> orbit_contents;
            for (const auto& node_id : merge_orbit.second) {
                if (merged_to_ta.find(node_id) != merged_to_ta.end()) {
                    orbit_contents.push_back(merged_to_ta.at(node_id));
                    ta_nodes_to_rep[merged_to_ta.at(node_id)] = ta_rep_id;
                }else{
                    std::cout << "Error: node_id not found in merged_to_ta" << std::endl;
                }
            }
            if (orbit_contents.size()>0){
                ta_orbits[ta_rep_id] = orbit_contents;

            }
        }
        if (merged_to_ata.find(merge_orbit.first) != merged_to_ata.end()){
            auto ata_rep_id = merged_to_ata.at(merge_orbit.first);
            std::vector< int> orbit_contents;
            for (const auto& node_id : merge_orbit.second) {
                if (merged_to_ata.find(node_id) != merged_to_ata.end()) {
                    orbit_contents.push_back(merged_to_ata.at(node_id));
                    ata_nodes_to_rep[merged_to_ata.at(node_id)] = ata_rep_id;
                }else{
                    std::cout << "Error: node_id not found in merged_to_ata" << std::endl;
                }
            }
            if (orbit_contents.size()>0){
                ata_orbits[ata_rep_id] = orbit_contents;

            }
        }
        if (merged_to_ta_action.find(merge_orbit.first) != merged_to_ta_action.end()){
            auto ta_rep_id = merged_to_ta_action.at(merge_orbit.first);
            std::vector< int> orbit_contents;
            for (const auto& node_id : merge_orbit.second) {
                if (merged_to_ta_action.find(node_id) != merged_to_ta_action.end()) {
                    orbit_contents.push_back(merged_to_ta_action.at(node_id));
                    ta_nodes_to_rep[merged_to_ta_action.at(node_id)] = ta_rep_id;
                }else{
                    std::cout << "Error: node_id not found in merged_to_ta_action" << std::endl;
                }
            }
            if (orbit_contents.size()>0){
                ta_orbits[ta_rep_id] = orbit_contents;

            }
        }
        if (merged_to_ata_action.find(merge_orbit.first) != merged_to_ata_action.end()){
            auto ata_rep_id = merged_to_ata_action.at(merge_orbit.first);
            std::vector< int> orbit_contents;
            for (const auto& node_id : merge_orbit.second) {
                if (merged_to_ata_action.find(node_id) != merged_to_ata_action.end()) {
                    orbit_contents.push_back(merged_to_ata_action.at(node_id));
                    ata_nodes_to_rep[merged_to_ata_action.at(node_id)] = ata_rep_id;
                }else{
                    std::cout << "Error: node_id not found in merged_to_ata_action" << std::endl;
                }
            }
            if (orbit_contents.size()>0){
                ata_orbits[ata_rep_id] = orbit_contents;

            }
        }
        
    }
    // std::map<std::vector<std::string>, std::string> labels_orb;
    // std::map< std::string, std::vector< std::string>> ta_label_orbits;
    // for (const auto &orb: ta_orbits){
    //     std::vector< std::string> labs;
    //     for (const auto &item: orb.second){
    //         auto la = ta_graph.getNodeLabel(item);
    //         labs.push_back(la);

    //     }
    //     if (labels_orb.find(labs)==labels_orb.end()){
    //         labels_orb[labs] = ta_graph.getNodeLabel(orb.first);
    //     }else{

    //     }
    // }


    std::unordered_map<int, std::vector<int>> newOrbits;
    newOrbits.reserve(ta_orbits.size());

    std::map<std::vector<std::string>, std::string> labels_orb;
    // std::map< std::string, std::vector< std::string>> ta_label_orbits;
    for (const auto &orb: ta_orbits){
        std::vector< std::string> labs;
        int rep_id = orb.first;
        for (const auto &item: orb.second){
            auto la = ta_graph.getNodeLabel(item);
            labs.push_back(la);

        }
        std::sort(labs.begin(), labs.end());
        if (labels_orb.find(labs)==labels_orb.end()){
            labels_orb[labs] = ta_graph.getNodeLabel(orb.first);
        }else{
            auto orb_rep_label = labels_orb[labs];
            for (const auto &item: orb.second){
                if (ta_graph.getNodeLabel(item)==orb_rep_label){
                    rep_id = item;
                }
            }
        }
        for (const auto &item: orb.second){
            ta_nodes_to_rep[item] = rep_id;

        }
        newOrbits[rep_id] = orb.second;

    }
    ta_orbits.swap(newOrbits);

    std::unordered_map<int, std::vector<int>> newATAorbits;
    newATAorbits.reserve(ata_orbits.size());

    //std::map<std::vector<std::string>, std::string> ata_labels_orb;
    //std::map< std::string, std::vector< std::string>> ata_label_orbits;
    for (const auto &orb: ata_orbits){
        std::vector< std::string> labs;
        int rep_id = orb.first;
        for (const auto &item: orb.second){
            auto la = ata_graph.getNodeLabel(item);
            labs.push_back(la);

        }
        std::sort(labs.begin(), labs.end());
        if (labels_orb.find(labs)==labels_orb.end()){
            labels_orb[labs] = ata_graph.getNodeLabel(orb.first);
        }else{
            auto orb_rep_label = labels_orb[labs];
            for (const auto &item: orb.second){
                if (ata_graph.getNodeLabel(item)==orb_rep_label){
                    rep_id = item;
                }
            }
        }
        for (const auto &item: orb.second){
            ata_nodes_to_rep[item] = rep_id;

        }
        newATAorbits[rep_id] = orb.second;

    }
    ata_orbits.swap(newATAorbits);

    auto taR = mergeOrbitsInGraph(ta_graph, ta_orbits);
    auto graph_ta_orb = std::get<0>(taR);
    auto rep_to_sim_ta = std::get<1>(taR);
    auto ataR = mergeOrbitsInGraph(ata_graph, ata_orbits);
    auto graph_ata_orb = std::get<0>(ataR);
    auto rep_to_sim_ata = std::get<1>(ataR);

    // for(const auto &orb: ata_orbits){
    //     std::cout<<"ata node rep: "<< ata_graph.getNodeLabel( orb.first)<<std::endl;
    //     for(const auto &inh : orb.second){
    //         std::cout<<"ata node inhalt: "<< ata_graph.getNodeLabel( inh)<<std::endl;

    //     }
    // }
    // for(const auto &orb: ta_orbits){
    //     std::cout<<"ta node rep: "<< ta_graph.getNodeLabel( orb.first)<<std::endl;
    //     for(const auto &inh : orb.second){
    //         std::cout<<"ta node inhalt: "<< ta_graph.getNodeLabel( inh)<<std::endl;

    //     }
    // }

    std::cout << "ta has " << ta.get_transitions().size()<<" trans." << std::endl;

    auto ta_ptr_and_map = tacos::automata::ta::buildTAFromGraph(graph_ta_orb);
    auto ta_ptr = std::get<0>(ta_ptr_and_map);
    auto ta_trans_to_transinfo = std::get<1>(ta_ptr_and_map);
    std::cout << "sim ta has " << ta_ptr->get_transitions().size()<<" trans." << std::endl;
    
    
    auto trans_ta = ta_ptr->get_transitions();
    std::map<tran_typ, std::vector<tran_typ>> transition_orbits;

    //build orbit of transition in quotient ta(rep) and transition in original ta( orbit content)
    for (const auto &tran :trans_ta){
        //std::cout<<tran.second<<std::endl;
        auto tran_info = ta_trans_to_transinfo.at(tran.second);
        int sim_tran_source = tran_info.source;
        int sim_tran_target = tran_info.target;
        int sim_tran_action = tran_info.action;
        int sim_tran_middle = tran_info.middle;
        auto sim_tran_clock_guards = tran_info.clock_guards;
        auto sim_tran_clock_reset = tran_info.reset;
        for (const auto &tran_org : taTrans_to_subgraph){
            auto org_tran_info = tran_org.second;

            
            int rep_org_source = ta_nodes_to_rep.at(org_tran_info.source);
            //std::cout<<rep_to_sim_ta.at(rep_org_source)<<std::endl;
            int rep_org_target = ta_nodes_to_rep.at(org_tran_info.target);
            //std::cout<<rep_to_sim_ta.at(rep_org_target)<<std::endl;

            int rep_org_action = ta_nodes_to_rep.at(org_tran_info.action);

            //std::cout<<rep_to_sim_ta.at(rep_org_action)<<std::endl;

            int rep_org_middle = ta_nodes_to_rep.at(org_tran_info.middle);
            //std::cout<<rep_to_sim_ta.at(rep_org_middle)<<std::endl;




            auto org_clock_guards = org_tran_info.clock_guards;
            auto org_clock_reset = org_tran_info.reset;
            if (rep_to_sim_ta.at(rep_org_source) == sim_tran_source &&
                rep_to_sim_ta.at(rep_org_target) == sim_tran_target &&
                rep_to_sim_ta.at(rep_org_action) == sim_tran_action &&
                rep_to_sim_ta.at(rep_org_middle) == sim_tran_middle){
                    std::unordered_map< int, std::vector< int>> tran_clock_guards_rep;
                    for (const auto& [guard, constraints] : org_clock_guards) {
                        std::vector< int> constraints_rep;
                        for ( int item : constraints) {
                            constraints_rep.push_back(rep_to_sim_ta.at(ta_nodes_to_rep.at(item)));
                        }
                        tran_clock_guards_rep[rep_to_sim_ta.at(ta_nodes_to_rep.at(guard))] = constraints_rep;
                    }

                    std::unordered_map< int, std::vector< int>> tran_clock_reset_rep;
                    for (const auto& [reset, clocks] : org_tran_info.reset) {
                        std::vector< int> clocks_rep;
                        for ( int item : clocks) {
                            clocks_rep.push_back(rep_to_sim_ta.at(ta_nodes_to_rep.at(item)));
                        }
                        tran_clock_reset_rep[rep_to_sim_ta.at(ta_nodes_to_rep.at(reset))] = clocks_rep;
                    }

                    if (compare_infos(sim_tran_clock_guards, tran_clock_guards_rep)&&
                        compare_infos(sim_tran_clock_reset, tran_clock_reset_rep)){
                            // 如果两个transition的轨道代表相同，则将它们添加到同一轨道中 
                            transition_orbits[tran.second].push_back(tran_org.first);
                            
                            
                    }
                }

        }
    }
    //std::cout << "ATA org:  " ;
    std::map<loc_typ, std::vector<loc_typ>> ta_loc_orbits;
    for (const auto &orbit : ta_orbits ){
        auto &rep = orbit.first;
        if (ta_graph.getNodeWithID(rep).type == NodeType::Location){
            //auto rep_str = ta_graph.getNodeLabel(rep);
            auto rep_loc = std::get<TALocationLabel<std::vector<std::string>>>(ta_graph.getNodeWithID(rep).label).get();
           
            //std::cout << "TA location: " << rep_loc << std::endl;
            //std::cout << "rep: " << rep_str << std::endl;
            //auto rep_loc = tacos::automata::ta::Location<std::vector<std::string>>(rep_str);
            std::vector<loc_typ> loc_orbit_content;
            for (const auto &loc : orbit.second){
                auto loc_label = std::get<TALocationLabel<std::vector<std::string>>>(ta_graph.getNodeWithID(loc).label).get();
                loc_orbit_content.push_back(tacos::automata::ta::Location<std::vector<std::string>>(loc_label));
                //std::cout << "location: " << loc_label << std::endl;
            }
            ta_loc_orbits[rep_loc] = loc_orbit_content;
        }

    }
    // std::map<ata_form_typ, std::vector<ata_form_typ>> ata_loc_orbits;
    // for (const auto &orbit : ata_orbits ){
    //     auto &rep = orbit.first;
    //     if (ata_graph.getNodeWithID(rep).type == NodeType::LocationFormula ||
    //         ata_graph.getNodeWithID(rep).type == NodeType::TrueFormula ||
    //         ata_graph.getNodeWithID(rep).type == NodeType::FalseFormula ||
    //         ata_graph.getNodeWithID(rep).type == NodeType::SinkLocation){
    //         //auto rep_str = ta_graph.getNodeLabel(rep);
    //         auto rep_loc = std::get<ATAFormLabel>(ata_graph.getNodeWithID(rep).label).get();
           
    //         //std::cout << "TA location: " << rep_loc << std::endl;
    //         //std::cout << "rep: " << rep_str << std::endl;
    //         //auto rep_loc = tacos::automata::ta::Location<std::vector<std::string>>(rep_str);
    //         std::vector<ata_form_typ> loc_orbit_content;
    //         for (const auto &loc : orbit.second){
    //             auto loc_label = std::get<ATAFormLabel>(ata_graph.getNodeWithID(loc).label).get();
    //             loc_orbit_content.push_back(tacos::automata::ta::Location<std::vector<std::string>>(loc_label));
    //             //std::cout << "location: " << loc_label << std::endl;
    //         }
    //         ata_loc_orbits[rep_loc] = loc_orbit_content;
    //     }

    // }

    for (const auto &loc :ta_ptr->get_locations()){
        if (ta_loc_orbits.find(loc) == ta_loc_orbits.end()){
            std::cout << "Location: " << loc <<  " miss! "<< std::endl;
        }
    }

   
    for(const auto &tran :ta_ptr->get_transitions()){
        if (transition_orbits.find(tran.second) == transition_orbits.end()){
            std::cout << "Transition: " << tran.second <<  " miss! "<< std::endl;
        }
    }
    auto ata_ptr = tacos::automata::ata::buildATAFromGraph(graph_ata_orb);
    std::cout << "sim ata has " << ata_ptr->get_transitions().size()<<" trans." << std::endl;
    

    // for (const auto &tran :ata_ptr->get_transitions()){
        
    //     std::cout << "Transition: " << *(tran.getFormula()) <<  " miss! "<< std::endl;
        
    // }
    std::cout<< ta_ptr->get_initial_location()<< " equal?  "<< ta.get_initial_location() << std::endl;
    std::cout<< ata_ptr->get_initial_location()<< " equal?  "<<  ata.get_initial_location() << std::endl;

    //std::cout << "TA sim:  " << *ta_ptr << std::endl;
    // result_automata result_ta = {ta_ptr,ta_orbits, ta_nodes_to_rep};
    // result_automata result_ata = {ata_ptr,ata_orbits, ata_nodes_to_rep};

    
    return std::make_tuple(ta_ptr, ata_ptr, ta_loc_orbits, transition_orbits );
    

}


template <typename LocationT, typename AP>
void printOrbits(const std::unordered_map< int, std::vector< int>> orbits,const Graph<LocationT, AP>& g){

    //int count = 0;
	std::cout << "Orbits:" << std::endl;
    auto adj = g.getAdjList();
	for (const auto &entry : orbits) {
		//count++; 
		std::cout << entry.first << "\n";
		if (entry.second.size() > 1) {
			//std::cout << "Orbit: ";
			
			for ( int v : entry.second) {
				auto n = g.getNodeWithID(v);
			
						// 输出节点 id 和 label
					std::cout<< "node id: " << n.id << ", type: " << static_cast<int>(n.type) << ", label: ";
					// label 是一个 variant，可以用 std::visit 打印
					std::visit([](auto &&val) {
						std::cout << val;
					}, n.label);
                    auto tgts = adj.at(v);
                    for (const auto& t : tgts){
                        auto t_n = g.getNodeWithID(t);
                        std::cout << " -> node id: "  << t_n.id << ", type: " << static_cast<int>(t_n.type) << ", label: ";
                        // label 是一个 variant，可以用 std::visit 打印
                        std::visit([](auto &&val) {
                            std::cout << val<< std::endl;
                        }, t_n.label);
                    }
                    

				
				
			}
			
			
		}
		else {
			continue;
		}
		
	}

}



template <typename LocationT, typename AP>
void printMiddelOrbits(const std::unordered_map< int, std::vector< int>> orbits,const Graph<LocationT, AP>& g){

    //int count = 0;
	std::cout << "Orbits:" << std::endl;
    auto adj = g.getAdjList();
	for (const auto &entry : orbits) {
		//count++; 
        if (g.getNodeWithID(entry.first).type == NodeType::TAMiddleNode ||
            g.getNodeWithID(entry.first).type == NodeType::ATAMiddleNode){
            std::cout << entry.first << "\n";
            if (entry.second.size() > 1) {
                //std::cout << "Orbit: ";
                
                for ( int v : entry.second) {
                    auto n = g.getNodeWithID(v);
                
                            // 输出节点 id 和 label
                        std::cout<< "node id: " << n.id << ", type: " << static_cast<int>(n.type) << ", label: ";
                        // label 是一个 variant，可以用 std::visit 打印
                        std::visit([](auto &&val) {
                            std::cout << val;
                        }, n.label);
                        auto tgts = adj.at(v);
                        for (const auto& t : tgts){
                            auto t_n = g.getNodeWithID(t);
                            std::cout << " -> node id: "  << t_n.id << ", type: " << static_cast<int>(t_n.type) << ", label: ";
                            // label 是一个 variant，可以用 std::visit 打印
                            std::visit([](auto &&val) {
                                std::cout << val<< std::endl;
                            }, t_n.label);
                        }
                        

                    
                    
                }
                
                
            }
            else {
                continue;
            }
            
        }
		
		
	}

}


template <typename LocationT, typename AP>
void print_action_Orbits(const std::unordered_map< int, std::vector< int>> orbits,const Graph<LocationT, AP>& g){

    //int count = 0;
	std::cout << "Orbits:" << std::endl;
    
	for (const auto &entry : orbits) {
		//count++; 
		
		if (entry.second.size() > 1) {
			//std::cout << "Orbit: ";
			
			for ( int v : entry.second) {
				auto n = g.getNodeWithID(v);
				if (n.type == NodeType::Controller_Action ||
                    n.type == NodeType::Environment_Action){ 
						// 输出节点 id 和 label
					std::cout << entry.first << "\n  node id: " << n.id 
							<< ", type: " << static_cast<int>(n.type)
							<< ", label: ";
					// label 是一个 variant，可以用 std::visit 打印
					std::visit([](auto &&val) {
						std::cout << val << std::endl;
					}, n.label);
				    
                }
				
			}
			
			
		}
		else {
			continue;
		}
		
	}

}


template <typename LocationT, typename AP>
std::unordered_map< int, std::vector< int>>
get_action_Orbits(const std::unordered_map< int, std::vector< int>> orbits,const Graph<LocationT, AP>& g){

    //int count = 0;
	//std::cout << "Orbits:" << std::endl;
    std::unordered_map< int, std::vector< int>> act_orbits;
	for (const auto &entry : orbits) {
		//count++; 
		
		if (g.getNodeWithID(entry.first).type == NodeType::Controller_Action ||
            g.getNodeWithID(entry.first).type == NodeType::Environment_Action) {
            //std::string label = tacos::automata::ata::formula_to_string(std::get<AP>(g.getNodeWithID(entry.first).label));
            //std::cout << "看看label：" << label << std::endl;
			act_orbits[entry.first] = entry.second;
			
		}
		else {
			continue;
		}
		
	}

    std::cout << " "<< std::endl;
    return act_orbits;

}

template <typename LocationT, typename AP>
std::unordered_map< int, std::vector< int>>
get_ta_location_Orbits(const std::unordered_map< int, std::vector< int>> orbits,const Graph<LocationT, AP>& g){

    //int count = 0;
	//std::cout << "Orbits:" << std::endl;
    std::unordered_map< int, std::vector< int>> loc_orbits;
	for (const auto &entry : orbits) {
		//count++; 
		
		if (g.getNodeWithID(entry.first).type == NodeType::Location ) {
            //std::cout << "看看loc类型有没有：" << entry.first << std::endl;
			loc_orbits[entry.first] = entry.second;
			
		}
		else {
			continue;
		}
		
	}
    return loc_orbits;

}

template <typename LocationT, typename AP>
std::unordered_map< int, std::vector< int>>
get_ata_location_Orbits(const std::unordered_map< int, std::vector< int>> orbits,const Graph<LocationT, AP>& g){

    //int count = 0;
	//std::cout << "Orbits:" << std::endl;
    std::unordered_map< int, std::vector< int>> loc_orbits;
	for (const auto &entry : orbits) {
		//count++; 
		
		if (g.getNodeWithID(entry.first).type == NodeType::LocationFormula ) {
            
			loc_orbits[entry.first] = entry.second;
			
		}
		else {
			continue;
		}
		
	}
    return loc_orbits;

}
