#ifndef ATA_CONVERSOR_HPP
#define ATA_CONVERSOR_HPP

#include "automata/ata.h"
#include "automata/ata_formula.h"
#include "graph.hpp"
#include "graph_types.hpp"
#include "mtl/MTLFormula.h"

#include <sstream>
#include <string>
#include <map>
#include <set>
#include <unordered_map>
#include <memory>
#include <iostream>
#include <functional>
#include <variant>
#include <stdexcept>




namespace tacos::automata::ata {
 // 辅助函数：利用 operator<< 将公式转换成字符串表示
// 为了兼容任意可输出类型，采用通用模板版本
template <typename T>
std::string formula_to_string(const T &formula) { 
    std::ostringstream oss;
    oss << formula;
    return oss.str();
}


template<typename T, typename Compare = std::less<T>, typename Alloc = std::allocator<T>>
std::set<T, Compare, Alloc> vectorToSet(std::vector<T, Alloc>&& vec) {
    // 利用 std::make_move_iterator 将 vector 中的元素移动到 set 中
    return std::set<T, Compare, Alloc>(
        std::make_move_iterator(vec.begin()),
        std::make_move_iterator(vec.end())
    );
}

// 辅助函数：从 ClockConstraint 中提取比较操作符和常量（常量类型为 unsigned）
template <typename LocationT>
void extractClockConstraintInfo(const ClockConstraint &constraint, std::string &opStr, unsigned &constVal) {
    std::visit([&](auto &c) {
         using T = std::decay_t<decltype(c)>;
         if constexpr (std::is_same_v<T, AtomicClockConstraintT<std::less<Time>>>) {
             opStr = "<";
         } else if constexpr (std::is_same_v<T, AtomicClockConstraintT<std::less_equal<Time>>>) {
             opStr = "≤";
         } else if constexpr (std::is_same_v<T, AtomicClockConstraintT<std::equal_to<Time>>>) {
             opStr = "=";
         } else if constexpr (std::is_same_v<T, AtomicClockConstraintT<std::not_equal_to<Time>>>) {
             opStr = "≠";
         } else if constexpr (std::is_same_v<T, AtomicClockConstraintT<std::greater_equal<Time>>>) {
             opStr = "≥";
         } else if constexpr (std::is_same_v<T, AtomicClockConstraintT<std::greater<Time>>>) {
             opStr = ">";
         }
         constVal = c.get_comparand();
    }, constraint);
}


template <typename LocationT, typename SymbolT>
Graph<LocationT, SymbolT> buildGraphFromATA(const AlternatingTimedAutomaton<LocationT, SymbolT>& ata, const std::set<std::string> &controller_actions) {
    Graph<LocationT, SymbolT> graph;
    std::unordered_map<std::string, int> formulaCache;

    // 1. 处理初始位置、接受位置、sink以及所有转移中出现的源位置
    int initialMarkerId = graph.addNode(MarkerLabel("ATAInitialLocation"), NodeType::ATAInitialLocation);
    
    auto initloc = ata.get_initial_location();
    // 直接使用 initloc 构造节点标签时，此处假设 graph.addNode 对 LocationT 有对应重载
    int stId = graph.addNode(ATALocationLabel(initloc), NodeType::LocationFormula);
    graph.addEdge(initialMarkerId, stId);
    formulaCache[formula_to_string(initloc)] = stId;
   

    int finalMarkerId = graph.addNode(MarkerLabel("ATAAcceptLocation"), NodeType::ATAacceptLocation);
    for (const auto &loc : ata.get_final_locations()) {
        if (formulaCache.find(formula_to_string(loc)) != formulaCache.end())
            continue;
        int apId = graph.addNode(ATALocationLabel(loc), NodeType::LocationFormula);
       // std::cout << "finalMarkerId: " << finalMarkerId << " final loc : " << formula_to_string(loc) << std::endl;
        graph.addEdge(finalMarkerId, apId);
        formulaCache[formula_to_string(loc)] = apId;
       
    }
    if (ata.get_sink_location().has_value()) {
        auto sinkVal = ata.get_sink_location().value();
        int sinkId = graph.addNode(ATALocationLabel(sinkVal), NodeType::SinkLocation);
        // 注意：此处 sinkVal 类型为 LocationT，但我们已经在 MarkerLabel 中存储了其字符串表示
        formulaCache[formula_to_string(sinkVal)] = sinkId;
       
    }
    // 2. 添加动作节点
    std::map<SymbolT, int> actionToId;
    for (const auto &symbol : ata.get_alphabet()) {
        int actId;
        if (controller_actions.find(formula_to_string(symbol)) != controller_actions.end()) {
            actId = graph.addNode(symbol, NodeType::Controller_Action);
        } else {
            actId = graph.addNode(symbol, NodeType::Environment_Action);

        }
        
        actionToId[symbol] = actId;
    }

    // 3. 全局缓存（公式缓存，确保相同公式只生成一个节点）
    //std::unordered_map<tacos::logic::MTLFormula<std::string>, int> formulaCache;
    
    std::map<std::string, int> clockVarCache;
    std::map<std::string, int> compOpCache;
    std::map<unsigned, int> constCache;
    int trueNodeCache = -1, falseNodeCache = -1;

    // 全局逻辑根节点（可选）
    int globalAndRoot = graph.addNode(MarkerLabel("and"), NodeType::LogicRoot);
    int globalOrRoot  = graph.addNode(MarkerLabel("or"), NodeType::LogicRoot);
    int formulaRoot = graph.addNode(MarkerLabel("formula"), NodeType::formularoot);
    // int dis = 0;
    // int con = 0;
    // 4. 定义递归函数 convertFormula
    // 对于 ATA 中的位置公式，我们直接保存其 raw 值（使用 ATALocationLabel）；对于其它公式类型，保存其字符串表示
    std::function<int(const Formula<LocationT>*)> convertFormula =
    [&](const Formula<LocationT>* formula) -> int {
        std::string key = formula_to_string(*formula);
        //auto key = *formula;
         auto it = formulaCache.find(key);  
         if (it != formulaCache.end()) {
            //std::cout << "Formula: get formula in Cache: " << key << std::endl;
            //std::cout << " " << std::endl;
            return it->second;
         }
         int nodeId = -1;
         if (dynamic_cast<const TrueFormula<LocationT>*>(formula)) {
             if (trueNodeCache != -1)
                 nodeId = trueNodeCache;
             else {
                 nodeId = graph.addNode(MarkerLabel("true"), NodeType::TrueFormula);
                 trueNodeCache = nodeId;
             }
            //std::cout << "trueNodeCache: " << trueNodeCache << std::endl;
            //std::cout << " " << std::endl;
         }
         else if (dynamic_cast<const FalseFormula<LocationT>*>(formula)) {
             if (falseNodeCache != -1)
                 nodeId = falseNodeCache;
             else {
                 nodeId = graph.addNode(MarkerLabel("false"), NodeType::FalseFormula);
                 falseNodeCache = nodeId;
             }
            //std::cout << "falseNodeCache: " << falseNodeCache << std::endl;
            //std::cout << " " << std::endl;
         }
         else if (auto lf = dynamic_cast<const LocationFormula<LocationT>*>(formula)) {
             // 修改：使用 ATALocationLabel 封装位置公式
            if (formulaCache.find(formula_to_string(lf->get_location())) != formulaCache.end()){
                return formulaCache[formula_to_string(lf->get_location())];
            }else{
                nodeId = graph.addNode(ATALocationLabel(lf->get_location()), NodeType::LocationFormula);
                formulaCache[formula_to_string(lf->get_location())] = nodeId;
            }
            //std::cout << "Formula: " << lf->get_location() << " " << nodeId << std::endl;
            //std::cout << " " << std::endl;
         }
         else if (auto cf = dynamic_cast<const ClockConstraintFormula<LocationT>*>(formula)) {
            nodeId = graph.addNode(MarkerLabel("ClockConstraint"), NodeType::ATAClockGuard);
            std::string clockVar = "x";
            int clockVarNode;
            if (clockVarCache.find(clockVar) == clockVarCache.end()) {
                clockVarNode = graph.addNode(ClockVarLabel(clockVar), NodeType::ATAClockVar);
                clockVarCache[clockVar] = clockVarNode;
            } else {
                clockVarNode = clockVarCache[clockVar];
            }
            std::string opStr;
            unsigned cVal = 0;
            extractClockConstraintInfo<LocationT>(cf->getConstraint(), opStr, cVal);
            int compOpNode;
            if (compOpCache.find(opStr) == compOpCache.end()) {
                compOpNode = graph.addNode(ComparisonOpLabel(opStr), NodeType::ATAComparisonOp);
                compOpCache[opStr] = compOpNode;
            } else {
                compOpNode = compOpCache[opStr];
            }
            int constNode;
            if (constCache.find(cVal) == constCache.end()) {
                constNode = graph.addNode(ConstantLabel(cVal), NodeType::ATAConstant);
                constCache[cVal] = constNode;
            } else {
                constNode = constCache[cVal];
            }

            // std::cout <<"ClockConstraint -->" << "clockVarNode: " << clockVarNode << std::endl;
            // std::cout <<"ClockConstraint -->" << "compOpNode: " << compOpNode << std::endl;
            // std::cout <<"ClockConstraint -->" << "constNode: " << constNode << std::endl;
            // std::cout << " " << std::endl;
            graph.addEdge(nodeId, clockVarNode);
            graph.addEdge(nodeId, compOpNode);
            graph.addEdge(nodeId, constNode);
         }
         else if (auto conj = dynamic_cast<const ConjunctionFormula<LocationT>*>(formula)) {
            nodeId = graph.addNode(MarkerLabel("and"), NodeType::LogicOp);
            //++con;
            // std::cout << "    " ;
            // std::cout << "ConjunctionFormula " << con <<" -->" << std::endl;
            int leftId = convertFormula(conj->getConjunct1().get());
            // std::cout << "    " ;
            // std::cout << "ConjunctionFormula " << con <<" -->" << std::endl;
            int rightId = convertFormula(conj->getConjunct2().get());
            graph.addEdge(nodeId, leftId);
            graph.addEdge(nodeId, rightId);
            graph.addEdge(globalAndRoot, nodeId);
            //std::cout << " " << std::endl;
         }
        else if (auto disj = dynamic_cast<const DisjunctionFormula<LocationT>*>(formula)) {
            // ++dis;
            // std::cout << "DisjunctionFormula " << dis <<" -->" << std::endl;
            nodeId = graph.addNode(MarkerLabel("or"), NodeType::LogicOp);
            // std::cout << "    " ;
            // std::cout << formula_to_string(*disj->getDisjunct1()) << std::endl;
            int leftId = convertFormula(disj->getDisjunct1().get());
            // std::cout << "    " ;
            // std::cout << "DisjunctionFormula " << dis <<" -->" << std::endl;
            // std::cout << formula_to_string(*disj->getDisjunct2()) << std::endl;
            int rightId = convertFormula(disj->getDisjunct2().get());
            
            graph.addEdge(nodeId, leftId);
            graph.addEdge(nodeId, rightId);
            graph.addEdge(globalOrRoot, nodeId);
            // --dis;
            // std::cout << "*****nodeID****: " <<nodeId<< std::endl;
         }
         else if (auto reset = dynamic_cast<const ResetClockFormula<LocationT>*>(formula)) {
            //std::cout << "ResetClockFormula --> ";
            nodeId = graph.addNode(MarkerLabel("ResetClock"), NodeType::ATAResetClock);
            //std::cout << "    " ;
            int subId = convertFormula(reset->getSubFormula().get());
            std::string clockVar = "x";
            int clockVarNode;
            if (clockVarCache.find(clockVar) == clockVarCache.end()) {
                clockVarNode = graph.addNode(ClockVarLabel(clockVar), NodeType::ATAClockVar);
                clockVarCache[clockVar] = clockVarNode;
            } else {
                clockVarNode = clockVarCache[clockVar];
            }
            //std::cout << "ResetClockFormula --> " << clockVar << std::endl;
            graph.addEdge(nodeId, clockVarNode);
            graph.addEdge(nodeId, subId);
            //std::cout << "ResetClockFormula --> " << std::endl;
         }
         else {
           std::cout << "unknown_formula" << std::endl;  
         }
         formulaCache[key] = nodeId;
         return nodeId;
    };

    // 5. 处理转移：格式为：源位置 -> 中间节点（动作） -> 公式节点
    int transCount = 0;
    for (const auto &t : ata.get_transitions()) {
        ++transCount;
        int sourceId = -1;

        if (formulaCache.find(formula_to_string(t.source_)) == formulaCache.end()) {
            // 修改：使用 ATALocationLabel封装 t.source_
            sourceId = graph.addNode(ATALocationLabel(t.source_), NodeType::LocationFormula);
        
            formulaCache[formula_to_string(t.source_)] = sourceId;
        } else {
            sourceId = formulaCache[formula_to_string(t.source_)];
        }
        //std::cout << "sourceId: " << sourceId << std::endl;
        //std::cout << "sourceNodeLabel: " << std::get<ATALocationLabel>(graph.getNodeWithID(sourceId).label).get() << std::endl;
        if (sourceId == -1)
            throw std::runtime_error("Source location not found");
        int transMiddleId = graph.addNode(t.symbol_, NodeType::ATAMiddleNode);
        //std::cout << "middleNodeLabel: " << std::get<SymbolT>(graph.getNodeWithID(transMiddleId).label)<< std::endl;
        graph.addEdge(sourceId, transMiddleId);
        graph.addEdge(actionToId[t.symbol_], transMiddleId);
        //std::cout << formula_to_string(*t.getFormula()) << std::endl;
        //std::cout << "sourceID:" << sourceId << "middleId: " << transMiddleId <<std::endl;

        int formulaId = convertFormula(t.getFormula());
        //std::cout << "middleId: " << transMiddleId << "formID: "<< formulaId << std::endl;

        //std::cout<<"公式id："<< formulaId<< std::endl;
        //t.printSourceAndSymbol();
        //std::cout << formula_to_string(*t.getFormula()) << std::endl;
       // std::cout << " " << std::endl;
        graph.addEdge(transMiddleId, formulaId);
        graph.addEdge(formulaRoot, formulaId);
//**************************************** */
        //std::cout << "sourceId: " << sourceId << " sourceNodeLabel: " << std::get<ATALocationLabel>(graph.getNodeWithID(sourceId).label).get()<< "-->" << " middleId: " << transMiddleId << "-->" <<" formID: "<< formulaId << " "<<formula_to_string(*t.getFormula()) << std::endl;
    }
    //std::cout << "transCount: " << transCount << std::endl;
//


    return graph;
}


//
// 以下 restore_formula_from_graph 和 buildATAFromGraph 
// 这里我们假设对于 LocationFormula 节点，label 存储的是 ATALocationLabel（即直接存储 ATA 的原始 LocationT），
// 并假定 LocationFormula 提供从 LocationT 构造的构造函数
//

template <typename LocationT, typename SymbolT>
std::unique_ptr<Formula<LocationT>> restore_formula_from_graph(const Graph<LocationT, SymbolT>& graph, int nodeId) {
    const auto& node = graph.getNodeWithID(nodeId);
    const auto& adj_list = graph.getAdjList();

    switch (node.type) {
        case NodeType::TrueFormula:
            return std::make_unique<TrueFormula<LocationT>>();
        case NodeType::FalseFormula:
            return std::make_unique<FalseFormula<LocationT>>();
        case NodeType::LocationFormula: {
            // 修改：从 ATALocationLabel 中提取原始的 LocationT
            auto loc = std::get<ATALocationLabel>(node.label).get();
            return std::make_unique<LocationFormula<LocationT>>(loc);
        }
        case NodeType::ATAClockGuard: {
            std::string clock_var, comp_op;
            unsigned const_val = 0;
            for (int child_id : adj_list.at(nodeId)) {
                 const auto &child = graph.getNodeWithID(child_id);
                 if (child.type == NodeType::ATAClockVar)
                      clock_var = std::get<ClockVarLabel>(child.label).get();
                 else if (child.type == NodeType::ATAComparisonOp)
                      comp_op = std::get<ComparisonOpLabel>(child.label).get();
                 else if (child.type == NodeType::ATAConstant)
                      const_val = std::get<ConstantLabel>(child.label);
            }
            if (comp_op == "<")
                 return std::make_unique<ClockConstraintFormula<LocationT>>(AtomicClockConstraintT<std::less<Time>>(const_val));
            else if (comp_op == "≤")
                 return std::make_unique<ClockConstraintFormula<LocationT>>(AtomicClockConstraintT<std::less_equal<Time>>(const_val));
            else if (comp_op == "=")
                 return std::make_unique<ClockConstraintFormula<LocationT>>(AtomicClockConstraintT<std::equal_to<Time>>(const_val));
            else if (comp_op == "≠")
                 return std::make_unique<ClockConstraintFormula<LocationT>>(AtomicClockConstraintT<std::not_equal_to<Time>>(const_val));
            else if (comp_op == "≥")
                 return std::make_unique<ClockConstraintFormula<LocationT>>(AtomicClockConstraintT<std::greater_equal<Time>>(const_val));
            else if (comp_op == ">")
                 return std::make_unique<ClockConstraintFormula<LocationT>>(AtomicClockConstraintT<std::greater<Time>>(const_val));
            else
                 throw std::runtime_error("Unknown comparison operator in ClockGuard node");
        }
        case NodeType::LogicOp: {
            //std::cout << "当前节点： " << nodeId << std::endl;
            auto children = adj_list.at(nodeId);
            // for (auto c : children){
            //     std::cout << "看看子节点是啥： " << c << std::endl;
            // }
            if (children.size() == 1)
                return restore_formula_from_graph<LocationT, SymbolT>(graph, children[0]);
            if (children.size() == 0)
                throw std::runtime_error("Malformed LogicOp node");
            auto left = restore_formula_from_graph<LocationT, SymbolT>(graph, children[0]);
            auto right = restore_formula_from_graph<LocationT, SymbolT>(graph, children[1]);
            std::string op = std::get<MarkerLabel>(node.label).get();
            if (op == "and")
                return create_conjunction<LocationT>(std::move(left), std::move(right));
            else if (op == "or")
                return create_disjunction<LocationT>(std::move(left), std::move(right));
            else
                throw std::runtime_error("Unknown logical operator in restoration");
        }
        case NodeType::ATAResetClock: {
            auto children = adj_list.at(nodeId);
            if (children.empty())
                throw std::runtime_error("Malformed ResetClock node");
            int subId = children.back();
            auto sub = restore_formula_from_graph<LocationT, SymbolT>(graph, subId);
            return std::make_unique<ResetClockFormula<LocationT>>(std::move(sub));
        }
        default:
            throw std::runtime_error("Unsupported node type in formula restoration");
    }
}

template <typename LocationT, typename SymbolT>
std::shared_ptr<AlternatingTimedAutomaton<LocationT, SymbolT>> buildATAFromGraph(const Graph<LocationT, SymbolT>& graph) {
    // 用 optional 暂存初始位置和 sink 位置
    std::optional<LocationT> initial_locationOpt;
    std::set<LocationT> final_locations;
    std::set<SymbolT> alphabet;
    std::optional<LocationT> sink_locationOpt;
    std::vector<Transition<LocationT, SymbolT>> transitions;
    auto adj = graph.getAdjList();
    //auto nodes = graph.getNodes();
    // 构造反向邻接表
    std::unordered_map<int, std::vector<int>> incoming;
    for (const auto &pair : graph.getAdjList()) {
        int src = pair.first;
        for (int dst : pair.second) {
            incoming[dst].push_back(src);
        }
    }
    //int count_re = 0;
    // 遍历所有节点
    //int middleNodeCount = 0;
   
    for (const auto& node : graph.getNodes()) {
        //auto node_Id = node.id;
        if (node.type == NodeType::ATAMiddleNode ){
            std::optional<LocationT> source_loc;
            std::optional<SymbolT> actionOpt;
            int form_id = -1;
            int source_id = -1;
            if (adj.find(node.id)!=adj.end()){
                if (adj.at(node.id).size()!=1){
                    for (int f_id : adj.at(node.id)){
                    
                       std::cout << node.id <<"  "<< graph.getNodeLabel(node.id) << "-->" << f_id <<"  "<< graph.getNodeLabel(f_id)<< std::endl; 
                    }
                    //throw std::runtime_error("one middel, two formula!");
                }else{
                    for (int f_id : adj.at(node.id)){

                        form_id = f_id;

                       // std::cout << "node ID: "<< node.id << "-->" << form_id << std::endl; 
                    // coun++;
                    }
                }
            }
            
            if (incoming.find(node.id)!=incoming.end()){
               
                for (int sou_id : incoming.at(node.id)){
                    if (graph.getNodeWithID(sou_id).type == NodeType::LocationFormula){
                        
                        source_id = sou_id;
                        //std::cout << "source ID" << sou_id << "-->" << node.id << std::endl; 
                        //coun++;
                    }
                    
                }
                

            }
            actionOpt = std::get<SymbolT>(node.label);
            source_loc = std::get<ATALocationLabel>(graph.getNodeWithID(source_id).label).get(); 
            auto t_formula = restore_formula_from_graph<LocationT, SymbolT>(graph, form_id);


            //*********************
            alphabet.insert(actionOpt.value());
            // auto form = Transition<LocationT, SymbolT>(source_loc.value(), actionOpt.value(), std::move(t_formula)).clone();
            // std::cout<< "form: "<< form << std::endl;
            transitions.emplace_back(source_loc.value(), actionOpt.value(), std::move(t_formula));

            //std::cout<<"coun: "<<coun<<std::endl;
            //++middleNodeCount;
        
        }
        else if (node.type == NodeType::ATAInitialLocation) {
            // ATA 初始位置：从其相邻节点中提取 ATALocationLabel 字符串
            if (adj.find(node.id) != adj.end() && !adj.at(node.id).empty()) {
                //graph.printNode(graph.getNodeWithID(adj.at(node.id)[0]));
                auto initStr = std::get<ATALocationLabel>(graph.getNodeWithID(adj.at(node.id)[0]).label).get(); // <-- 修改处
                auto init_ptr = std::make_unique<LocationFormula<LocationT>>(initStr);
                initial_locationOpt = init_ptr->get_location();
            }
        }
        else if (node.type == NodeType::ATAacceptLocation) {
            // ATA 接受位置：遍历所有相邻节点，构造 LocationT 对象后加入集合
            if (adj.find(node.id) != adj.end()) {
                for (int final_loc_id : adj.at(node.id)) {
                    auto finalStr = std::get<ATALocationLabel>(graph.getNodeWithID(final_loc_id).label).get(); // <-- 修改处
                    auto final_ptr = std::make_unique<LocationFormula<LocationT>>(finalStr);
                    final_locations.insert(final_ptr->get_location());
                }
            }
        }
        else if (node.type == NodeType::Controller_Action ||
                 node.type == NodeType::Environment_Action ) {
            // 收集 alphabet
            if (adj.find(node.id) != adj.end()) {
                alphabet.insert(std::get<SymbolT>(graph.getNodeWithID(node.id).label));
                
            }
        }
        else if (node.type == NodeType::SinkLocation) {
            // Sink 位置：修改为使用 ATALocationLabel
            
            auto sinkStr = std::get<ATALocationLabel>(node.label).get(); // <-- 修改处
            auto sink_ptr = std::make_unique<LocationFormula<LocationT>>(sinkStr);
            sink_locationOpt = sink_ptr->get_location();
        }
        
    }

    if (!initial_locationOpt.has_value()) {
        throw std::runtime_error("No initial location found in graph");
    }
    //std::cout << "count_re: " << count_re << std::endl;
    //std::cout << "middleNodeCount: " << middleNodeCount << std::endl;

    
    return std::make_shared<AlternatingTimedAutomaton<LocationT, SymbolT>>(
        alphabet,
        *initial_locationOpt,
        final_locations,
        vectorToSet(std::move(transitions)),
        sink_locationOpt
    );
}

} // namespace tacos::automata::ata




#endif // ATA_CONVERSOR_HPP
