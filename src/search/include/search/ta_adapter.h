/***************************************************************************
 *  ta_adapter.h - Generate successors of TA configurations
 *
 *  Created:   Thu  9 Sep 09:52:44 CEST 2021
 *  Copyright  2021  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/

#pragma once

#include "adapter.h"
#include "canonical_word.h"
#include "utilities/types.h"

#include <spdlog/spdlog.h>

#include <vector>

namespace tacos::search {

/** Short-hand type alias for a configuration of a TA */
template <typename LocationT>
using TAConfiguration = automata::ta::TAConfiguration<LocationT>;

/** An expanded state (location, clock_name, clock_valuation) of a TA. */
template <typename LocationT>
using TAState = PlantState<automata::ta::Location<LocationT>>;

/** @brief Compute all TA symbol successors for one particular time successor.
 *
 * Compute the successors by following all transitions in the TA and ATA for one time successor
 * and all possible symbols.
 * This is a partial template specialization of the generic plant adapter.
 * */
template <typename LocationT,
          typename ActionType,
          typename ConstraintSymbolType,
          bool use_location_constraints,
		  bool use_set_semantics>
class get_next_canonical_words<automata::ta::TimedAutomaton<LocationT, ActionType>,
                               ActionType,
                               ConstraintSymbolType,
                               use_location_constraints,
							   use_set_semantics>
{
public:
	/** Construct the comparator with the given action partitioning.
	 * @param controller_actions The actions that the controller can select
	 * @param environment_actions The actions that the environment can select
	 */
	get_next_canonical_words([[maybe_unused]] const std::set<ActionType> &controller_actions  = {},
	                         [[maybe_unused]] const std::set<ActionType> &environment_actions = {},
							 [[maybe_unused]] const std::set<ActionType> &symbols = {})
							 : symbols(symbols)
							 
	{
	}

	
	/** Get the next canonical words. */
	std::multimap<
	  ActionType,
	  CanonicalABWord<typename automata::ta::TimedAutomaton<LocationT, ActionType>::Location,
	                  ConstraintSymbolType>>
	operator()(
	  const automata::ta::TimedAutomaton<LocationT, ActionType> &ta,
	  const automata::ata::AlternatingTimedAutomaton<logic::MTLFormula<ConstraintSymbolType>,
	                                                 logic::AtomicProposition<ConstraintSymbolType>>
	                                                          &ata,
	  const std::pair<typename automata::ta::TimedAutomaton<LocationT, ActionType>::Configuration,
	                  ATAConfiguration<ConstraintSymbolType>> &ab_configuration,
	  const RegionIndex,
	  const RegionIndex K)
	{
		static_assert(use_location_constraints || std::is_same_v<ActionType, ConstraintSymbolType>);
		static_assert(
		  !use_location_constraints
		  || std::is_same_v<typename automata::ta::TimedAutomaton<LocationT, ActionType>::Location,
		                    ConstraintSymbolType>);
		std::multimap<
		  ActionType,
		  CanonicalABWord<typename automata::ta::TimedAutomaton<LocationT, ActionType>::Location,
		                  ConstraintSymbolType>>
		  successors;


		  //std::cout<<"传进来的参数 symbols："<<std::endl;

		  for(const auto &s :symbols){
			std::cout<<"action:  "<<s<<std::endl;
		  }
		std::set<ActionType> alphates;
		if (!symbols.empty()){
			alphates = symbols;
		}else{
			alphates = ta.get_alphabet();
		}
		
		for (const auto &symbol : alphates) {
			// std::cout<<"  "<<std::endl;
			// std::cout<<"action:  "<<symbol<<std::endl;
			SPDLOG_TRACE("({}, {}): Symbol {}", ab_configuration.first, ab_configuration.second, symbol);
			const std::set<typename automata::ta::TimedAutomaton<LocationT, ActionType>::Configuration>
			  ta_successors = ta.make_symbol_step(ab_configuration.first, symbol);

			//std::cout<<ab_configuration.first<<std::endl;
            // // ATA侧：先将 symbol（假设类型为std::string）转换为字符串，然后根据 action_map转换
            // std::string symbol_str = symbol; // 假设 ActionType 可转换为 std::string
            // tacos::logic::AtomicProposition<std::string> ata_symbol(symbol_str);
            // auto it = action_map.find(symbol_str);
            // if (it != action_map.end()) {
            //     ata_symbol = it->second;
            // }




			std::set<ATAConfiguration<ConstraintSymbolType>> ata_successors;
			if constexpr (!use_location_constraints) {
				//ata_successors = ata.make_symbol_step(ab_configuration.second, ata_symbol);
				ata_successors = ata.make_symbol_step(ab_configuration.second, symbol);
			}
			SPDLOG_TRACE("({}, {}): TA successors: {} ATA successors: {}",
			             ab_configuration.first,
			             ab_configuration.second,
			             ta_successors.size(),
			             ata_successors.size());
			for (const auto &ta_successor : ta_successors) {
				SPDLOG_TRACE("({}, {}): TA successor {}",
				             ab_configuration.first,
				             ab_configuration.second,
				             ta_successor);
				if constexpr (use_location_constraints) {
					ata_successors = ata.make_symbol_step(ab_configuration.second,
					                                      logic::AtomicProposition{ta_successor.location});
				}
				for (const auto &ata_successor : ata_successors) {
					SPDLOG_TRACE("({}, {}): ATA successor {}",
					             ab_configuration.first,
					             ab_configuration.second,
					             ata_successor);
					[[maybe_unused]] auto successor = successors.insert(
					  std::make_pair(symbol, get_canonical_word(ta_successor, ata_successor, K)));
					SPDLOG_TRACE("({}, {}): Getting {} with symbol {}",
					             ab_configuration.first,
					             ab_configuration.second,
					             successor->second,
					             symbol);
				}
			}
		}
		return successors;
	}

	private:

    const std::set<ActionType> symbols;
};

} // namespace tacos::search
