#ifndef TA_GRAPH_TYPES_HPP
#define TA_GRAPH_TYPES_HPP

#include <string>
#include <variant>
#include <NamedType/named_type.hpp>
#include "automata/ta.h"
#include "automata/ata.h"
#include "mtl/MTLFormula.h"


// --------------------- 1) 节点类型枚举 ---------------------
enum class NodeType {
    TAInitialLocation, // TA initial location marker 0
    ATAInitialLocation,  // ATA initial loc marker 1

    TAacceptLocation,  // TA accept loc marker 2
    ATAacceptLocation,  // ATA accept loc marker 3

    TAResetClock,      // TA重置时钟 4
    TAClockGuard,      // TA时钟约束中间节点 5

    Location,        // TA地点 6
    Action,          // 动作（TA与ATA共用） 7
    TAClockVar,        // 时钟变量 (TA专用) 8
    TAComparisonOp,    // TA比较操作符  9
    TAConstant,         // TA常数值  10
    TAMiddleNode,       // TA中间节点 11

    //ATA node type
    LogicOp,          // 逻辑操作符 12
    LogicRoot,        // 逻辑根节点 13
    formularoot,     // 根节点 14
    SinkLocation,   // Sink位置 15
    LocationFormula,    // 地点公式 16
    TrueFormula,        // True 17
    FalseFormula,       // False 18
    ATAResetClock,      // ATA重置时钟 19
    ATAClockGuard,      // ATA时钟约束中间节点 20
    ATAClockVar,        // ATA时钟变量 21
    ATAMiddleNode,       // ATA中间节点 22
    ATAComparisonOp,     //ATA比较操作符 23
    ATAConstant,           //ATA常数 24

    Controller_Action, // 控制器动作 25
    Environment_Action // 环境动作 26
};

using MarkerLabel = fluent::NamedType<std::string, struct MarkerTag, fluent::Printable>;
using ResetClockLabel = fluent::NamedType<std::string, struct ResetClockTag, fluent::Printable>;
using ClockGuardLabel = fluent::NamedType<std::string, struct ClockGuardTag, fluent::Printable>;
using ClockVarLabel = fluent::NamedType<std::string, struct ClockVarTag, fluent::Printable>;
using ComparisonOpLabel = fluent::NamedType<std::string, struct ComparisonOpTag, fluent::Printable>;
using Middellabel = fluent::NamedType<std::string, struct MiddelTag, fluent::Printable>;
using ConstantLabel = unsigned int;

// ATA 特有标签类

using ATALocationLabel = fluent::NamedType<tacos::logic::MTLFormula<std::string> , struct ATALocationTag, fluent::Printable>;

template <typename LocationT>
using TALocationLabel = fluent::NamedType<tacos::automata::ta::Location<LocationT>, struct TALocationTag, fluent::Printable>;


// 修改 NodeLabel，确保各 alternative 唯一：
template <typename LocationT, typename AP>
using NodeLabel = std::variant<
    MarkerLabel,                                       // 用于 InitialLocation、AcceptLocation 标记
    TALocationLabel<LocationT>,          // 地点
    AP,                                                // 动作
    ResetClockLabel,                                   // 重置时钟节点
    ClockGuardLabel,                                   // 时钟约束节点
    ClockVarLabel,                                     // 时钟变量
    ComparisonOpLabel,                                 // 比较操作符
    ConstantLabel,                                      // 常数值                      
    ATALocationLabel                                    // ATA 地点
>;




#endif