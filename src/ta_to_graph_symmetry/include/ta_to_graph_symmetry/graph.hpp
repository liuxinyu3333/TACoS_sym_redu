#ifndef TA_GRAPH_HPP
#define TA_GRAPH_HPP

#include "graph_types.hpp"
#include <vector>
#include <unordered_map>
#include <fstream>
#include <sstream>
#include <stdexcept>
#include <cstdlib>



template <typename LocationT, typename AP>
struct GraphNode {
    int id;
    NodeLabel<LocationT, AP> label;
    NodeType type;
};


template <typename LocationT, typename AP>
class Graph
{
public:
    // 添加新节点，利用模板重载允许传入任意类型
    template<typename T>
    int addNode(const T &value, NodeType type) {
        return addNodeImpl(value, type, -1);
    }

    template<typename T>
    int addNode(const T &value, NodeType type, int specifiedId) {
        return addNodeImpl(value, type, specifiedId);
    }

    // 添加有向边 from -> to
    void addEdge(int from, int to) {
        std::vector<int>& edges = adj_list[from];
    // 如果 to 不在列表中，则添加
        if (std::find(edges.begin(), edges.end(), to) == edges.end()) {
            edges.push_back(to);
        }
    }
    void changeLabel(int id, const NodeLabel<LocationT, AP>& new_label) {
        // 先更新 nodeMap 中存储的节点
        nodeMap.at(id).label = new_label;
        // 遍历 nodes 向量，找到对应 id 的节点并修改 label
        for (auto &node : nodes) {
            if (node.id == id) {
                node.label = new_label;
                break; // 找到后退出循环
            }
        }
    }
    GraphNode<LocationT, AP> getNodeWithID(int id) const {
        return nodeMap.at(id);
    }

    // 访问节点列表
    const std::vector<GraphNode<LocationT, AP>>& getNodes() const {
        return nodes;
    }

    // 访问邻接表
    const std::unordered_map<int, std::vector<int>>& getAdjList() const {
        return adj_list;
    }

    const std::unordered_map<int, GraphNode<LocationT, AP>>& getNodeMap() const {
        return nodeMap;
    }

    void printNode(const GraphNode<LocationT, AP>& node) const {
        
        std::cout << "Node: " << node.id << ", Type: " << static_cast<int>(node.type) << ", Label: ";
        std::visit([](auto&& val) {
            std::cout << val;
        }, node.label);
        std::cout << std::endl;
        
    }

    std::string getNodeLabel(int id) const {
        auto it = nodeMap.find(id);
        if (it != nodeMap.end()) {
            std::ostringstream oss;
            std::visit([&oss](auto&& val) {
                oss << val;
            }, it->second.label);
            return oss.str();
        }
        throw std::invalid_argument("Node ID not found.");
    }

    void printNodes() {
        for (const auto& node : nodes) {
            printNode(node);
        }
    }


        // 将 graph 对象导出为 DOT 文件
    void exportGraphToDot(const std::string& dotFilename) {
        std::ofstream ofs(dotFilename);
        if (!ofs) {
            throw std::runtime_error("无法打开文件: " + dotFilename);
        }
        // DOT 文件开始部分（构造有向图）
        ofs << "digraph G {" << "\n";
        
        // 输出所有节点的信息
        for (const auto& node : nodes) {
            // 使用ostringstream生成节点标签文本
            std::ostringstream labelStream;
            labelStream << "node id: " << node.id
                        << ", type: " << static_cast<int>(node.type)
                        << ", label: ";
            // 利用 std::visit 遍历 label 的变体，输出其中的值
            std::visit([&labelStream](auto &&val) {
                labelStream << val;
            }, node.label);
            std::string labelStr = labelStream.str();
            // 在 DOT 中定义节点，节点名称可以以 node_<id> 命名，标签属性用 [label="..."]
            ofs << "  node_" << node.id << " [label=\"" << labelStr << "\"];\n";
        }
        
        // 输出所有边的信息
        for (const auto& entry : adj_list) {
            int from = entry.first;
            for (int to : entry.second) {
                ofs << "  node_" << from << " -> node_" << to << ";\n";
            }
        }
        ofs << "}" << "\n";
    }


        // 通过调用 Graphviz 的 dot 命令生成图片

    void generateGraphImage(const std::string& dotFilename,
                            const std::string& outputImageFile) {
        // 先将图导出为 DOT 文件
        exportGraphToDot(dotFilename);
        // 构造调用命令，生成 PNG 图片
        std::string command = "dot -Tpng " + dotFilename + " -o " + outputImageFile;
        int ret = system(command.c_str());
        if (ret != 0) {
            throw std::runtime_error("dot fail:" + std::to_string(ret));
        }
    }
    // std::vector<std::vector<int>> findSymmetry(std::unordered_map<int, std::vector<int>> adj_list, std::string partition) {
    //     std::vector<std::vector<int>> orbits;
    //     std::cout << "Finding symmetries..." << std::endl;
    //     const std::string dreadnaut_path = "/home/xinyuliu/nauty2_8_9/dreadnaut";
    //     std::ostringstream oss;
    //     oss << "Ad\nd\nn=" << nodes.size() << " g\n";
    //     for (int i = 0; i < static_cast<int>(nodes.size()); ++i) {
    //         oss << i << ": ";
    //         if (adj_list.find(i) != adj_list.end()) {
    //             for (auto tgt : adj_list[i]) {
    //                 oss << tgt << " ";
    //             }
    //         }
    //         oss << ";\n";
    //     }
    //     oss << "f=" << partition << "\n";
    //     oss << "x\no\nq\n";
    //     std::cout << "写入输入文件." << std::endl;
    //     // 写入输入文件
    //     std::ofstream input_file("graph.in");
    //     if (!input_file.is_open()) {
    //         throw std::runtime_error("Failed to open graph.in for writing.");
    //     }
    //     input_file << oss.str();
    //     input_file.close();
    //     std::cout << "调用 dreadnaut 命令." << std::endl;
    //     // 调用 dreadnaut 命令
    //     const std::string command = dreadnaut_path + " < graph.in > result.out";
    //     int ret_code = std::system(command.c_str());
    //     if (ret_code != 0) {
    //         throw std::runtime_error("Error executing dreadnaut. Return code: " + std::to_string(ret_code));
    //     }
    //     std::cout << "解析 dreadnaut 输出." << std::endl;
    //     // 解析 dreadnaut 输出
    //     std::ifstream result_file("result.out");
    //     if (!result_file.is_open()) {
    //         throw std::runtime_error("Failed to open result.out for reading.");
    //     }
    
    //     std::ostringstream output;
    //     bool found_cpu_time = false;
    //     std::string line;
    
    //     while (std::getline(result_file, line)) {
    //         if (!found_cpu_time && line.find("cpu time") != std::string::npos) {
    //             found_cpu_time = true;
    //             continue;
    //         }
    //         if (found_cpu_time) {
    //             output << line;
    //         }
    //     }
    //     result_file.close();
    
    //     // 解析轨道数据
    //     std::stringstream ss(output.str());
    //     std::string segment;
    
    //     while (std::getline(ss, segment, ';')) {
    //         std::vector<int> orbit;
    //         std::stringstream orbit_stream(segment);
    //         int value;
    
    //         while (orbit_stream >> value) {
    //             orbit.push_back(value);
    //         }
    //         orbits.push_back(orbit);
    //     }
    
    //     return orbits;
    // }

     // 新增：导出 DOT 文件函数
private:
    std::vector<GraphNode<LocationT, AP>> nodes;
    std::unordered_map<int, std::vector<int>> adj_list;
    std::unordered_map<int, GraphNode<LocationT, AP>> nodeMap;

    template<typename T>
    int addNodeImpl(const T &value, NodeType type, int specifiedId) {
        NodeLabel<LocationT, AP> label = value;
        int newId;

        if (specifiedId == -1) {
            newId = static_cast<int>(nodes.size());
        } else {
            newId = specifiedId;
            if (nodeMap.find(newId) != nodeMap.end()) {
                throw std::invalid_argument("Node ID already exists.");
            }
        }

        nodes.push_back({ newId, label, type });
        nodeMap[newId] = { newId, label, type };
        adj_list[newId] = {};
        return newId;
    }


   
};


#endif /* ifndef TA_GRAPH_HPP */