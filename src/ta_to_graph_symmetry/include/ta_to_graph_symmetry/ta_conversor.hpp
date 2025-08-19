#ifndef TA_CONVERSOR_HPP
#define TA_CONVERSOR_HPP

#include "graph.hpp"
//需要进行模块化操作

#include "automata/ata.h"

inline tacos::automata::ClockConstraint makeClockConstraint(const std::string &opSymbol, unsigned int constantVal) {
    if(opSymbol == "<")
        return tacos::automata::AtomicClockConstraintT<std::less<tacos::Time>>(constantVal);
    else if(opSymbol == "≤")
        return tacos::automata::AtomicClockConstraintT<std::less_equal<tacos::Time>>(constantVal);
    else if(opSymbol == "=")
        return tacos::automata::AtomicClockConstraintT<std::equal_to<tacos::Time>>(constantVal);
    else if(opSymbol == "≠")
        return tacos::automata::AtomicClockConstraintT<std::not_equal_to<tacos::Time>>(constantVal);
    else if(opSymbol == "≥")
        return tacos::automata::AtomicClockConstraintT<std::greater_equal<tacos::Time>>(constantVal);
    else if(opSymbol == ">")
        return tacos::automata::AtomicClockConstraintT<std::greater<tacos::Time>>(constantVal);
    else
        throw std::runtime_error("Unknown comparison operator: " + opSymbol);
}


namespace tacos::automata::ta {
/**
 * @brief 将 TimedAutomaton 转化为 Graph。
 *
 * 结构示例：
 *   Marker (InitialLocation) -> Location -> Action -> Location
 *   Action -> ResetClock -> ClockVar    (重置时钟)
 *   Action -> ClockGuard -> {ClockVar, ComparisonOp, Constant} (时钟约束)
 * 在构造各节点时，均使用相应的命名类型包装，确保还原时类型完全匹配 TA 的定义。
 */

struct TransitionSubgraphInfo {
    int source;       // 源位置节点ID
   // std::unordered_map<unsigned int, unsigned int> action;   // 动作节点ID
    int middle; 
    int target;       // 目标位置节点ID
    int action;       // 全局动作节点ID
    std::unordered_map<int, std::vector<int>> clock_guards;   // 时间约束节点IDs
    std::unordered_map<int, std::vector<int>> reset;   // 时间约束节点IDs

};

template <typename LocationT, typename AP>
std::pair<Graph<LocationT, AP>, std::map<automata::ta::Transition<LocationT, AP>, TransitionSubgraphInfo>> 
 buildGraphFromTA(const TimedAutomaton<LocationT, AP> &ta, const std::set<std::string> &controller_actions )
{
    Graph<LocationT, AP> graph;
    //using Transition = automata::ta::Transition<LocationT, AP>;
    int initialMarkerId = graph.addNode(MarkerLabel("InitialLocation"), NodeType::TAInitialLocation);
    int acceptMarkerId  = graph.addNode(MarkerLabel("AcceptLocation"), NodeType::TAacceptLocation);
    std::cout << "acceptMarkerId: " << acceptMarkerId << " AcceptLocation"<< std::endl;
    std::map<automata::ta::Location<LocationT>, int> locationToId;
    for(const auto & loc : ta.get_locations()) {
        int locId = graph.addNode(TALocationLabel<LocationT>(loc), NodeType::Location);
        locationToId[loc] = locId;
    }

    std::map<AP, int> actionToId;

    //*********************************************** */
    for(const auto & act : ta.get_alphabet()) {
        int actId;
        if (controller_actions.find(act) != controller_actions.end()) {
            actId = graph.addNode(act, NodeType::Controller_Action);
        } else {
            actId = graph.addNode(act, NodeType::Environment_Action);

        }
        
        actionToId[act] = actId;
    }

    // accept loc：AcceptLocation marker -> final location
    for(const auto & floc : ta.get_final_locations()) {
        int fLocId = locationToId.at(floc);
        graph.addEdge(acceptMarkerId, fLocId);
    }
    int initLocId = locationToId.at(ta.get_initial_location());
    graph.addEdge(initialMarkerId, initLocId);

    // cache of ClockVar、ComparisonOp、Constant 节点
    std::map<std::string, int> clockVarCache;
    std::map<std::string, int> compOpCache;
    std::map<unsigned int, int> constCache;
    std::map<automata::ta::Transition<LocationT, AP>, TransitionSubgraphInfo> transitionSubgraphs;

    std::size_t transitionIndex = 0;

    // 遍历所有转移
    for (auto it = ta.get_transitions().begin(); it != ta.get_transitions().end(); ++it, ++transitionIndex) {
        const auto & sourceLoc = it->first;
        const auto & trans     = it->second;

        //std::cout<<"trans: " << trans.source_ <<"; first: " << sourceLoc << std::endl;
        int srcId    = locationToId.at(sourceLoc);
        int actionId = actionToId.at(trans.symbol_);
        int tgtId    = locationToId.at(trans.target_);
        int middelId = graph.addNode(trans.symbol_, NodeType::TAMiddleNode);

        // transition： Location -> MiddleNode -> Target Location, Action -> MiddleNode
        graph.addEdge(srcId, middelId);
        graph.addEdge(middelId, tgtId);
        graph.addEdge(actionId, middelId);

        //build subgraph
        TransitionSubgraphInfo subgraphInfo;
        subgraphInfo.source = srcId;
        subgraphInfo.middle = middelId;
        subgraphInfo.target = tgtId;
        subgraphInfo.action = actionId;

     

        // reset clock ： MiddleNode -> ResetClock -> ClockVar
        int resetNodeId = graph.addNode(ResetClockLabel("TAResetClock"), NodeType::TAResetClock);
       // subgraphInfo.reset = resetNodeId;
        graph.addEdge(middelId, resetNodeId);
        for(const auto & resetClockName : trans.clock_resets_) {
            int clockVarId;
            if(clockVarCache.find(resetClockName) == clockVarCache.end()) {
                clockVarId = graph.addNode(ClockVarLabel(resetClockName), NodeType::TAClockVar);

                clockVarCache[resetClockName] = clockVarId;
            } else {
                clockVarId = clockVarCache[resetClockName];
            }
            graph.addEdge(resetNodeId, clockVarId);
            subgraphInfo.reset[resetNodeId].push_back(clockVarId);
        }

        // clock constraints： MiddelNode -> ClockGuard -> {ClockVar, ComparisonOp, Constant}
        for(const auto & guard : trans.clock_constraints_) {
            int cgId = graph.addNode(ClockGuardLabel("TAClockGuard"), NodeType::TAClockGuard);
            graph.addEdge(middelId, cgId);

            const std::string & clockName = guard.first;
            int clockVarId;
            if(clockVarCache.find(clockName) == clockVarCache.end()) {
                clockVarId = graph.addNode(ClockVarLabel(clockName), NodeType::TAClockVar);
                clockVarCache[clockName] = clockVarId;
            } else {
                clockVarId = clockVarCache[clockName];
            }

            std::string opSymbol;
            std::visit([&opSymbol](auto &c){
                using T = std::decay_t<decltype(c)>;
                if constexpr (std::is_same_v<T, tacos::automata::AtomicClockConstraintT<std::less<tacos::Time>>>) {
                    opSymbol = "<";
                } else if constexpr (std::is_same_v<T, tacos::automata::AtomicClockConstraintT<std::less_equal<tacos::Time>>>) {
                    opSymbol = "≤";
                } else if constexpr (std::is_same_v<T, tacos::automata::AtomicClockConstraintT<std::equal_to<tacos::Time>>>) {
                    opSymbol = "=";
                } else if constexpr (std::is_same_v<T, tacos::automata::AtomicClockConstraintT<std::not_equal_to<tacos::Time>>>) {
                    opSymbol = "≠";
                } else if constexpr (std::is_same_v<T, tacos::automata::AtomicClockConstraintT<std::greater_equal<tacos::Time>>>) {
                    opSymbol = "≥";
                } else if constexpr (std::is_same_v<T, tacos::automata::AtomicClockConstraintT<std::greater<tacos::Time>>>) {
                    opSymbol = ">";
                }
            }, guard.second);

            int compOpId;
            if(compOpCache.find(opSymbol) == compOpCache.end()) {
                compOpId = graph.addNode(ComparisonOpLabel(opSymbol), NodeType::TAComparisonOp);
                compOpCache[opSymbol] = compOpId;
            } else {
                compOpId = compOpCache[opSymbol];
            }

            unsigned int constVal = std::visit([](auto &c){ return c.get_comparand(); }, guard.second);
            int constId;
            if(constCache.find(constVal) == constCache.end()) {
                constId = graph.addNode(constVal, NodeType::TAConstant);
                constCache[constVal] = constId;
            } else {
                constId = constCache[constVal];
            }

            graph.addEdge(cgId, clockVarId);
            graph.addEdge(cgId, compOpId);
            graph.addEdge(cgId, constId);
            subgraphInfo.clock_guards[cgId].push_back(clockVarId);
            subgraphInfo.clock_guards[cgId].push_back(compOpId);
            subgraphInfo.clock_guards[cgId].push_back(constId);
           
        }

        transitionSubgraphs[trans] = subgraphInfo;
    }

    return  {graph, transitionSubgraphs}; // 返回主图和子图集合

}

// --------------------- 7) 从有向图恢复时间自动机的函数 ---------------------
template <typename LocationT, typename AP>
std::tuple< std::shared_ptr<TimedAutomaton<LocationT, AP>>, std::map<automata::ta::Transition<LocationT, AP>, TransitionSubgraphInfo>> 
buildTAFromGraph(const Graph<LocationT, AP>& graph)
{
    // 构建 id -> GraphNode 映射
    //尝试使用graph.getNodeMap()获取nodeMap可能会更好
    std::unordered_map<int, GraphNode<LocationT, AP>> nodeMap = graph.getNodeMap();


    std::map<automata::ta::Transition<LocationT, AP>, TransitionSubgraphInfo> transitionSubgraphs;
        //std::cout <<"nodes size: "<<graph.getNodeMap().size() << std::endl;
    //auto nodes = graph.getNodes();
    // for(const auto &node : graph.getNodes()){
    //     nodeMap[node.id] = node;
    // }
    // 构建反向邻接表：target -> {source}
    std::unordered_map<int, std::vector<int>> incoming;
    for(const auto &pair : graph.getAdjList()){
        int src = pair.first;
        for(int dst : pair.second){
            incoming[dst].push_back(src);
        }
    }
    //std::cout <<"构建反向完毕邻接表 " << std::endl;
    const auto &adj = graph.getAdjList();

    // 1. 查找初始位置标记节点 (InitialLocation) 及其出边确定真实初始位置
    int initMarkerId = -1;
    for(const auto &node : graph.getNodes()){
        if(node.type == NodeType::TAInitialLocation){
            initMarkerId = node.id;
            break;
        }
    }
   

    // for(const auto &p : nodeMap){
    //     std::cout << "TA node id: " << p.second.id << " type: "<< static_cast<int>(p.second.type) << std::endl;
    //     if(p.second.type == NodeType::TAInitialLocation){

    //         std::cout << "found!!   TA node id: " << p.second.id << " type: "<< static_cast<int>(p.second.type) << std::endl;
    //         initMarkerId = p.first;
    //         break;
    //     }
    // }
    if(initMarkerId == -1) throw std::runtime_error("No TA InitialLocation marker found.");
    if(adj.find(initMarkerId) == adj.end() || adj.at(initMarkerId).empty())
        throw std::runtime_error("TA InitialLocation marker has no outgoing edge.");
    int initLocId = adj.at(initMarkerId)[0];

    // 2. 查找接受位置标记节点 (AcceptLocation) 及其出边确定终止位置集合
    int acceptMarkerId = -1;
    for(const auto &node : graph.getNodes()){
        if(node.type == NodeType::TAacceptLocation){
            acceptMarkerId = node.id;
            break;
        }
    }
    // for(const auto &p : nodeMap){
    //     if(p.second.type == NodeType::TAacceptLocation){
    //         acceptMarkerId = p.first;
    //         break;
    //     }
    // }
    std::set<int> finalLocIds;
    if(acceptMarkerId != -1 && adj.find(acceptMarkerId) != adj.end()){
        for(int locId : adj.at(acceptMarkerId)){
            if(graph.getNodeWithID(locId).type == NodeType::Location)
                finalLocIds.insert(locId);
        }
    }

    // 3. 分别保存 Location 与 Action 节点（提取 TA 类型）
    std::unordered_map<int, LocationT> locationLabels;
    std::unordered_map<int, AP> actionLabels;
    for(const auto &p : nodeMap){
        if(p.second.type == NodeType::Location)
            locationLabels[p.first] = std::get<TALocationLabel<LocationT>>(p.second.label).get();
        else if(p.second.type == NodeType::TAMiddleNode)
            actionLabels[p.first] = std::get<AP>(p.second.label);
    }

    // 4. 构造地点集合与动作集合
    std::set<tacos::automata::ta::Location<LocationT>> locSet;
    for(const auto &p : locationLabels){
        locSet.insert(tacos::automata::ta::Location<LocationT>(p.second));
    }
    std::set<AP> actSet;
    for(const auto &p : actionLabels){
        actSet.insert(p.second);
    }
    tacos::automata::ta::Location<LocationT> initLocation(locationLabels[initLocId]);
    std::set<tacos::automata::ta::Location<LocationT>> finalLocSet;
    for(int fid : finalLocIds){
        finalLocSet.insert(tacos::automata::ta::Location<LocationT>(locationLabels[fid]));
    }

    // 5. 构造转移列表：遍历每个 Action 节点，根据其入边和出边构造转移，
    //    并提取 ResetClock 与 ClockGuard 信息
    std::vector<Transition<LocationT, AP>> transitions;
    std::set<std::string> clocks;
    for(const auto &actPair : actionLabels){
        int actionId = actPair.first;
        AP actLabel = actPair.second;

        TransitionSubgraphInfo subgraphInfo;

        
        subgraphInfo.middle = actionId;

        // 入边（来源为 Location）
        std::set<int> srcIds;
        if(incoming.find(actionId) != incoming.end()){
            for(int src : incoming.at(actionId)){
                if(nodeMap[src].type == NodeType::Location){
                    srcIds.insert(src);
                    subgraphInfo.source = src;
                }
                if(nodeMap[src].type == NodeType::Controller_Action || nodeMap[src].type == NodeType::Environment_Action){
                    
                    subgraphInfo.action = src;
                }
            }
        }
        if (srcIds.size() != 1){
            std::cout << "Error: action node " << actionId << " has multiple incoming edges." << std::endl;
        }
        // 出边（指向 Location）
        std::set<int> tgtIds;
        if(adj.find(actionId) != adj.end()){
            for(int tgt : adj.at(actionId)){
                if(nodeMap[tgt].type == NodeType::Location){
                    tgtIds.insert(tgt);
                    subgraphInfo.target = tgt;
                }
            }
        }
        if (tgtIds.size() != 1){
            std::cout << "Error: action node " << actionId << " has multiple outgoing edges." << std::endl;
        }

        
        // 重置：Action -> ResetClock -> ClockVar
        std::set<std::string> resets;
        if(adj.find(actionId) != adj.end()){
            for(int out : adj.at(actionId)){
                if(nodeMap[out].type == NodeType::TAResetClock){

                    if(adj.find(out) != adj.end()){
                        for(int cv : adj.at(out)){
                            if(nodeMap[cv].type == NodeType::TAClockVar){
                                resets.insert(std::get<ClockVarLabel>(nodeMap[cv].label).get());
                                clocks.insert(std::get<ClockVarLabel>(nodeMap[cv].label).get());
                                subgraphInfo.reset[out].push_back(cv);
                            }
                        }
                    }
                }
            }
        }
        // 时钟约束：Action -> ClockGuard -> {ClockVar, ComparisonOp, Constant}
        std::multimap<std::string, tacos::automata::ClockConstraint> guards;
        if(adj.find(actionId) != adj.end()){
            for(int out : adj.at(actionId)){
                if(nodeMap[out].type == NodeType::TAClockGuard){
                    std::string guardClock, guardOp;
                    unsigned int guardConst = 0;
                    if(adj.find(out) != adj.end()){
                        for(int child : adj.at(out)){
                            NodeType ct = nodeMap[child].type;
                            if(ct == NodeType::TAClockVar){
                                guardClock = std::get<ClockVarLabel>(nodeMap[child].label).get();
                                subgraphInfo.clock_guards[out].push_back(child);
                            }else if(ct == NodeType::TAComparisonOp){ 
                                guardOp = std::get<ComparisonOpLabel>(nodeMap[child].label).get();
                                subgraphInfo.clock_guards[out].push_back(child);
                            }else if(ct == NodeType::TAConstant){
                                guardConst = std::get<ConstantLabel>(nodeMap[child].label);
                                subgraphInfo.clock_guards[out].push_back(child);
                            }
                        }
                    }
                    if(!guardClock.empty() && !guardOp.empty()){
                        tacos::automata::ClockConstraint cst = makeClockConstraint(guardOp, guardConst);
                        guards.insert({guardClock, cst});
                        clocks.insert(guardClock);
                    }
                }
            }
        }
        // 组合入边和出边构造转移
        for(int srcId : srcIds){
            for(int tgtId : tgtIds){
                Transition<LocationT, AP> tran(
                    tacos::automata::ta::Location<LocationT>(locationLabels[srcId]),
                    actLabel,
                    tacos::automata::ta::Location<LocationT>(locationLabels[tgtId]),
                    guards,   // clock constraints
                    resets    // clock resets
                );
                transitions.push_back(tran);
                transitionSubgraphs[tran] = subgraphInfo;
                
                
            }
        }
    }

    TimedAutomaton<LocationT, AP> ta_result(locSet, actSet, initLocation, finalLocSet, clocks, transitions);
    return std::make_tuple(std::make_shared<TimedAutomaton<LocationT, AP>>(ta_result), transitionSubgraphs );
}

}

#endif