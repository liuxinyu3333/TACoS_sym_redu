#pragma once

#include "automata/ta.h"
#include "automata/automata.h"  // for is_satisfiable
#include <set>
#include <map>
#include <vector>
#include <algorithm>

namespace tacos::search {

/**
 * 构造 原 TA 与 Controller 的同步积，
 * Controller 的状态类型 CtrlLoc 可能 与 OrigLoc 不同。
 *
 * @tparam OrigLoc 原 TA 的 Location 类型
 * @tparam CtrlLoc Controller（商 TA）的 Location 类型
 * @tparam Action  动作类型
 */
template<
    typename OrigLoc,
    typename CtrlLoc,
    typename Action
>
tacos::automata::ta::TimedAutomaton<
    std::pair<OrigLoc, CtrlLoc>,  // product-location 类型
    Action
>
synchronous_product_with_mapping(
    const tacos::automata::ta::TimedAutomaton<OrigLoc, Action> &origTA,
    const tacos::automata::ta::TimedAutomaton<CtrlLoc, Action> &ctrl,
    const std::map<OrigLoc, std::set<OrigLoc>>                &loc_map,
    const std::map<
        tacos::automata::ta::Transition<OrigLoc, Action>,
        std::set<tacos::automata::ta::Transition<OrigLoc, Action>>
    >                                                         &trans_map
) {
    using ProdLoc    = std::pair<OrigLoc, CtrlLoc>;
    using ProdTA     = tacos::automata::ta::TimedAutomaton<ProdLoc, Action>;
    using Location   = tacos::automata::ta::Location<ProdLoc>;
    using Transition = tacos::automata::ta::Transition<ProdLoc, Action>;
    using ClockConst = tacos::automata::ClockConstraint;

    // 1) 构造所有 product-states
    std::set<Location> locations;
    for (auto const &q : ctrl.get_locations()) {
        auto it = loc_map.find(q);
        if (it == loc_map.end()) continue;
        for (auto const &p : it->second) {
        locations.insert(Location{ProdLoc{p,q}});
        }
    }

    // 2) 构造接收集
    std::set<Location> accepting;
    for (auto const &q : ctrl.get_final_locations()) {
        auto it = loc_map.find(q);
        if (it==loc_map.end()) continue;
        for (auto const &p: it->second) {
        if (origTA.get_final_locations().count(p)) {
            accepting.insert(Location{ProdLoc{p,q}});
        }
        }
    }

    // 3) 字母表 & 时钟并集
    std::set<Action> alphabet = origTA.get_alphabet();
    alphabet.insert(ctrl.get_alphabet().begin(), ctrl.get_alphabet().end());
    std::set<std::string> clocks = origTA.get_clocks();
    {
        auto &cw = const_cast<std::set<std::string>&>(clocks);
        cw.insert(ctrl.get_clocks().begin(), ctrl.get_clocks().end());
    }

    // 4) 初始状态
    OrigLoc o0 = origTA.get_initial_location();
    CtrlLoc q0 = ctrl.get_initial_location();
    Location init{ProdLoc{o0,q0}};

    // 5) 构造转移
    std::vector<Transition> transitions;

    for (auto const &loc : locations) {
        auto [p,q] = loc.get();

        // Controller 从 q 出发的转移区间
        auto [cb, ce] = ctrl.get_transitions().equal_range(q);
        for (auto itc = cb; itc != ce; ++itc) {
            auto const &c_tr = itc->second;
            Action        a  = c_tr.get_label();
            CtrlLoc       target = c_tr.get_target();
            CtrlLoc       source = itc->first;
            // 找到它对应的所有原 TA 转移
            auto [plantCfg_src, ataCfg_src] = tacos::search::get_candidate(source.get());
            auto [plantCfg_tgt, ataCfg_tgt] = tacos::search::get_candidate(target.get());
            for (const auto &tran_orbit : trans_map){
                auto tran_rep = tran_orbit.first;
                auto quo_src = tran_rep.get_source();
                auto quo_tgt = tran_rep.get_target();
                auto quo_action = tran_rep.get_label();

            }
                auto tmIt = trans_map.find(c_tr);
            if (tmIt == trans_map.end()) continue;



            for (auto const &o_tr : tmIt->second) {
                // 源必须匹配 p
                if (o_tr.get_source() != p) continue;

                // 合并 guards
                auto guards = o_tr.get_guards();
                guards.insert(c_tr.get_guards().begin(), c_tr.get_guards().end());
                if (!tacos::automata::is_satisfiable(guards)) continue;

                // 合并 resets
                std::set<std::string> resets = o_tr.get_reset();
                {
                auto &r = const_cast<std::set<std::string>&>(resets);
                r.insert(c_tr.get_reset().begin(), c_tr.get_reset().end());
                }

                OrigLoc p2 = o_tr.get_target();
                transitions.emplace_back(
                Location{ProdLoc{p,   q }},
                a,
                Location{ProdLoc{p2, q2}},
                guards,
                resets
                );
            }
        }
    }

    // 6) 返回产品 TA
    return ProdTA{
        locations,
        alphabet,
        init,
        accepting,
        clocks,
        transitions
    };
}

} // namespace tacos::search
