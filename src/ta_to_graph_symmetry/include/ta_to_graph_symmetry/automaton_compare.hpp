#include <algorithm>
#include <vector>
#include <map>
#include <set>
//#include "automata/ata.hpp"
// 假设 TA 对象类型定义为：
// template <typename LocationT, typename AP>
// class TimedAutomaton { ... };
//
// 且它提供了如下接口：
//  const std::set<AP>&         get_alphabet() const;
//  const std::set<Location>&   get_locations() const;
//  const Location&             get_initial_location() const;
//  const std::set<Location>&   get_final_locations() const;
//  const std::set<std::string>& get_clocks() const;
//  const std::multimap<Location, Transition<LocationT, AP>>& get_transitions() const;
//
// 同时 Transition 类已经定义了 operator== 和 operator<（用于排序比较）。

template <typename LocationT, typename AP>
bool are_ta_equal(const tacos::automata::ta::TimedAutomaton<LocationT, AP>& ta1,
                  const tacos::automata::ta::TimedAutomaton<LocationT, AP>& ta2) {
    if (ta1.get_alphabet() != ta2.get_alphabet()) {
        return false;
    }
    if (ta1.get_locations() != ta2.get_locations()) {
        return false;
    }
    
    if (ta1.get_initial_location() != ta2.get_initial_location()) {
        return false;
    }
    if (ta1.get_final_locations() != ta2.get_final_locations()) {
        return false;
    }
    if (ta1.get_clocks() != ta2.get_clocks()) {
        return false;
    }

    const auto& transitions1 = ta1.get_transitions();
    const auto& transitions2 = ta2.get_transitions();

    if (transitions1.size() != transitions2.size()) {
        return false;
    }

    // 由于转换存储在 multimap 中，为了确保顺序一致，我们将所有转换提取到 vector 中并排序后进行比较
    using Transition = typename tacos::automata::ta::Transition<LocationT, AP>;
    std::vector<Transition> vec1, vec2;
    for (const auto& p : transitions1) {
        vec1.push_back(p.second);
    }
    for (const auto& p : transitions2) {
        vec2.push_back(p.second);
    }
    std::sort(vec1.begin(), vec1.end());
    std::sort(vec2.begin(), vec2.end());
    
    return vec1 == vec2;
}


template <typename LocationT, typename SymbolT>
bool are_ata_equal(const  tacos::automata::ata::AlternatingTimedAutomaton<LocationT, SymbolT>& lhs,
               const  tacos::automata::ata::AlternatingTimedAutomaton<LocationT, SymbolT>& rhs) {
    std::ostringstream oss;
    bool equal = true;


    if (lhs.get_alphabet() != rhs.get_alphabet()) {
        return false;
    }


    if (lhs.get_initial_location() != rhs.get_initial_location()) {
        return false;
    }

   
    if (lhs.get_final_locations() != rhs.get_final_locations()) {
        return false;
    }
   
    if (lhs.get_sink_location() != rhs.get_sink_location()) {
        return false;
    }

   
    const auto& lhs_transitions = lhs.get_transitions();
    const auto& rhs_transitions = rhs.get_transitions();

    if (lhs_transitions.size() != rhs_transitions.size()) {
        return false;
    }

    
    auto it1 = lhs_transitions.begin();
    auto it2 = rhs_transitions.begin();
    int index = 0;
    while (it1 != lhs_transitions.end() && it2 != rhs_transitions.end()) {
        bool trans_equal = true;
        std::ostringstream trans_diff;
        
        if (it1->source_ != it2->source_) {
            trans_equal = false;
            trans_diff << "  Transition " << index << " source mismatch: lhs = " << it1->source_
                        << ", rhs = " << it2->source_ << "\n";
        }
        
        if (it1->symbol_ != it2->symbol_) {
            trans_equal = false;
            trans_diff << "  Transition " << index << " symbol mismatch: lhs = " << it1->symbol_
                        << ", rhs = " << it2->symbol_ << "\n";
        }
        
        if (!(*(it1->getFormula()) == *(it2->getFormula()))) {
            trans_equal = false;
            trans_diff << "  Transition " << index << " formula mismatch: lhs = " << *(it1->getFormula())
                        << ", rhs = " << *(it2->getFormula()) << "\n";
        }
        if (!trans_equal) {
            equal = false;
            oss << trans_diff.str();
        }
        ++it1;
        ++it2;
        ++index;
    }
    //std::cout << "detail: "<< oss.str() << " ";
    return equal;
}

