/***************************************************************************
 *  translator.hpp - Translate an MTL formula into an ATA
 *
 *  Created: Thu 18 Jun 2020 11:21:13 CEST 11:21
 *  Copyright  2020  Till Hofmann <hofmann@kbsg.rwth-aachen.de>
 *  SPDX-License-Identifier: LGPL-3.0-or-later
 ****************************************************************************/

#pragma once

#include "automata/ata.h"
#include "automata/ata_formula.h"
#include "automata/automata.h"
#include "mtl/MTLFormula.h"
#include "translator.h"
#include "utilities/powerset.h"

#include <fmt/format.h>

#include <memory>
#include <stdexcept>

namespace tacos::mtl_ata_translation {

using namespace automata;
using logic::AtomicProposition;
using logic::LOP;
using logic::MTLFormula;
using logic::TimeInterval;

///@{
/// Formulas are always ATA formulas over MTLFormulas.
template <typename ConstraintSymbolT>
using Formula = ata::Formula<MTLFormula<ConstraintSymbolT>>;
template <typename ConstraintSymbolT>
using TrueFormula = ata::TrueFormula<MTLFormula<ConstraintSymbolT>>;
template <typename ConstraintSymbolT>
using FalseFormula = ata::FalseFormula<MTLFormula<ConstraintSymbolT>>;
template <typename ConstraintSymbolT>
using ConjunctionFormula = ata::ConjunctionFormula<MTLFormula<ConstraintSymbolT>>;
template <typename ConstraintSymbolT>
using ResetClockFormula = ata::ResetClockFormula<MTLFormula<ConstraintSymbolT>>;
template <typename ConstraintSymbolT>
using DisjunctionFormula = ata::DisjunctionFormula<MTLFormula<ConstraintSymbolT>>;
template <typename ConstraintSymbolT>
using LocationFormula = ata::LocationFormula<MTLFormula<ConstraintSymbolT>>;
template <typename ConstraintSymbolT>
using ClockConstraintFormula = ata::ClockConstraintFormula<MTLFormula<ConstraintSymbolT>>;
///@}

///@{
/// The resulting type is an ATA over MTLFormulas and AtomicPropositions.
template <typename LocationT, typename SymbolT>
using ATA = ata::AlternatingTimedAutomaton<MTLFormula<LocationT>, AtomicProposition<SymbolT>>;
template <typename LocationT, typename SymbolT>
using T = ata::Transition<MTLFormula<LocationT>, AtomicProposition<SymbolT>>;
///@}

using utilities::arithmetic::BoundType;

/** Compute the closure of a formula.
 * A sub-formula is part of the closure if its operator type is until or dual until.
 */
template <typename ConstraintSymbolT>
std::set<MTLFormula<ConstraintSymbolT>>
get_closure(const MTLFormula<ConstraintSymbolT> &formula)
{
	auto untils      = formula.get_subformulas_of_type(LOP::LUNTIL);
	auto dual_untils = formula.get_subformulas_of_type(LOP::LDUNTIL);
	untils.insert(dual_untils.begin(), dual_untils.end());
	return untils;
}

/// Creates constraint defining the passed interval
template <typename ConstraintSymbolT>
std::unique_ptr<Formula<ConstraintSymbolT>>
create_contains(TimeInterval duration)
{
	std::unique_ptr<Formula<ConstraintSymbolT>> lowerBound =
	  std::make_unique<TrueFormula<ConstraintSymbolT>>();
	std::unique_ptr<Formula<ConstraintSymbolT>> upperBound =
	  std::make_unique<TrueFormula<ConstraintSymbolT>>();
	if (duration.lowerBoundType() != BoundType::INFTY) {
		if (duration.lowerBoundType() == BoundType::WEAK) {
			lowerBound = std::make_unique<ClockConstraintFormula<ConstraintSymbolT>>(
			  AtomicClockConstraintT<std::greater_equal<Time>>(duration.lower()));
		} else {
			lowerBound = std::make_unique<ClockConstraintFormula<ConstraintSymbolT>>(
			  AtomicClockConstraintT<std::greater<Time>>(duration.lower()));
		}
	}
	if (duration.upperBoundType() != BoundType::INFTY) {
		if (duration.upperBoundType() == BoundType::WEAK) {
			upperBound = std::make_unique<ClockConstraintFormula<ConstraintSymbolT>>(
			  AtomicClockConstraintT<std::less_equal<Time>>(duration.upper()));
		} else {
			upperBound = std::make_unique<ClockConstraintFormula<ConstraintSymbolT>>(
			  AtomicClockConstraintT<std::less<Time>>(duration.upper()));
		}
	}
	return ata::create_conjunction(std::move(lowerBound), std::move(upperBound));
}

/// Creates constraint excluding the passed interval
template <typename ConstraintSymbolT>
std::unique_ptr<Formula<ConstraintSymbolT>>
create_negated_contains(TimeInterval duration)
{
	std::unique_ptr<Formula<ConstraintSymbolT>> lowerBound =
	  std::make_unique<FalseFormula<ConstraintSymbolT>>();
	std::unique_ptr<Formula<ConstraintSymbolT>> upperBound =
	  std::make_unique<FalseFormula<ConstraintSymbolT>>();
	if (duration.lowerBoundType() != BoundType::INFTY) {
		if (duration.lowerBoundType() == BoundType::WEAK) {
			lowerBound = std::make_unique<ClockConstraintFormula<ConstraintSymbolT>>(
			  AtomicClockConstraintT<std::less<Time>>(duration.lower()));
		} else {
			lowerBound = std::make_unique<ClockConstraintFormula<ConstraintSymbolT>>(
			  AtomicClockConstraintT<std::less_equal<Time>>(duration.lower()));
		}
	}
	if (duration.upperBoundType() != BoundType::INFTY) {
		if (duration.upperBoundType() == BoundType::WEAK) {
			upperBound = std::make_unique<ClockConstraintFormula<ConstraintSymbolT>>(
			  AtomicClockConstraintT<std::greater<Time>>(duration.upper()));
		} else {
			upperBound = std::make_unique<ClockConstraintFormula<ConstraintSymbolT>>(
			  AtomicClockConstraintT<std::greater_equal<Time>>(duration.upper()));
		}
	}
	return ata::create_disjunction(std::move(lowerBound), std::move(upperBound));
}

/** The init function, as defined by Ouaknine and Worrell, 2005. */
template <typename ConstraintSymbolT, typename SymbolT, bool state_based>
std::unique_ptr<Formula<ConstraintSymbolT>>
init(const MTLFormula<ConstraintSymbolT> &formula,
     const AtomicProposition<SymbolT>    &ap,
     bool                                 first = false)
{
	static_assert(state_based || std::is_same_v<SymbolT, ConstraintSymbolT>);
	static_assert(!state_based || std::is_same_v<SymbolT, std::set<ConstraintSymbolT>>);
	switch (formula.get_operator()) {
	case LOP::TRUE: return std::make_unique<TrueFormula<ConstraintSymbolT>>();
	case LOP::FALSE: return std::make_unique<FalseFormula<ConstraintSymbolT>>();
	case LOP::LUNTIL:
	case LOP::LDUNTIL:
		// init(psi, a) = x.psi if psi \in cl(phi)
		if (first) {
			return std::make_unique<LocationFormula<ConstraintSymbolT>>(formula);
		} else {
			return std::make_unique<ResetClockFormula<ConstraintSymbolT>>(
			  std::make_unique<LocationFormula<ConstraintSymbolT>>(formula));
		}
	case LOP::LAND: {
		std::vector<std::unique_ptr<Formula<ConstraintSymbolT>>> conjuncts;
		for (const auto &conjunct : formula.get_operands()) {
			conjuncts.push_back(init<ConstraintSymbolT, SymbolT, state_based>(conjunct, ap, first));
		}
		return ata::create_conjunction(std::move(conjuncts));
	}
	case LOP::LOR: {
		// init(psi_1 OR psi_2, a) = init(psi_1, a) OR init(psi_2, a)
		std::vector<std::unique_ptr<Formula<ConstraintSymbolT>>> disjuncts;
		for (const auto &disjunct : formula.get_operands()) {
			disjuncts.push_back(init<ConstraintSymbolT, SymbolT, state_based>(disjunct, ap, first));
		}
		return ata::create_disjunction(std::move(disjuncts));
	}
	case LOP::AP:
		if constexpr (state_based) {
			if (ap.ap_.find(formula.get_atomicProposition().ap_) != ap.ap_.end()) {
				// init(b, a) = TRUE if b is contained in a
				return std::make_unique<TrueFormula<ConstraintSymbolT>>();
			} else {
				// init(b, a) = FALSE if b is not contained in a
				return std::make_unique<FalseFormula<ConstraintSymbolT>>();
			}
		} else {
			if (formula == ap) {
				// init(b, a) = TRUE if b == a
				return std::make_unique<TrueFormula<ConstraintSymbolT>>();
			} else {
				// init(b, a) = FALSE if b != a
				return std::make_unique<FalseFormula<ConstraintSymbolT>>();
			}
		}
	case LOP::LNEG:
		// init(NOT b, a) = NOT init(b, a)
		// ATA formulas do not have negations, directly compute the result.
		// We know that this is an atomic proposition because the input formula is in positive normal
		// form.
		switch (formula.get_operands().front().get_operator()) {
		case LOP::TRUE: return std::make_unique<FalseFormula<ConstraintSymbolT>>();
		case LOP::FALSE: return std::make_unique<TrueFormula<ConstraintSymbolT>>();
		case LOP::AP:
			if constexpr (state_based) {
				if (ap.ap_.find(formula.get_operands().front().get_atomicProposition().ap_)
				    != ap.ap_.end()) {
					// init(b, a) = FALSE if b is contained in a
					return std::make_unique<FalseFormula<ConstraintSymbolT>>();
				} else {
					// init(b, a) = TRUE if b is not contained in a
					return std::make_unique<TrueFormula<ConstraintSymbolT>>();
				}
			} else {
				if (formula.get_operands().front() == ap) {
					// init(b, a) = TRUE if b == a
					return std::make_unique<FalseFormula<ConstraintSymbolT>>();
				} else {
					// init(b, a) = FALSE if b != a
					return std::make_unique<TrueFormula<ConstraintSymbolT>>();
				}
			}
		default:
			std::stringstream ss;
			ss << "The formula " << formula << " is not in positive normal form.";
			throw std::logic_error(ss.str());
		}
	}
	throw std::logic_error("Unexpected formula operator");
}

/** Get the initial location of the ATA. */
template <typename ConstraintSymbolT>
AtomicProposition<ConstraintSymbolT>
get_l0()
{
	return AtomicProposition{ConstraintSymbolT{{"l0"}}};
}

/** Get the sink location of the ATAs. */
template <typename ConstraintSymbolT>
AtomicProposition<ConstraintSymbolT>
get_sink()
{
	return AtomicProposition{ConstraintSymbolT{{"sink"}}};
}

/** Compute the ATA alphabet for the given input alphabet.
 * Depending on whether we are using state-based or event-based constraints, the ATA alphabet is
 * either the same as the input alphabet, or its powerset.
 * @param input_alphabet The symbols used in the constraints
 * @return A set of atomic propositions, which can be used as alphabet of the ATA */
template <bool state_based, typename ConstraintSymbolT>
auto
compute_alphabet(std::set<AtomicProposition<ConstraintSymbolT>> input_alphabet)
{
	auto unwrap = [](std::set<AtomicProposition<ConstraintSymbolT>> input) {
		std::set<ConstraintSymbolT> res;
		for (const auto &i : input) {
			res.insert(i.ap_);
		}
		return res;
	};
	auto wrap = [](std::set<std::set<ConstraintSymbolT>> input) {
		std::set<AtomicProposition<std::set<ConstraintSymbolT>>> res;
		for (const auto &i : input) {
			res.insert(AtomicProposition{i});
		}
		return res;
	};

	if constexpr (state_based) {
		return wrap(utilities::construct_powerset(unwrap(input_alphabet)));
	} else {
		return input_alphabet;
	}
}
/** Translate an MTL formula into an ATA.
 * Create the ATA closely following the construction by Ouaknine and Worrell, 2005.
 * @param input_formula The formula to translate
 * @param input_alphabet The alphabet that the ATA should read, defaults to the symbols of the
 * formula.
 * @return An ATA that accepts a word w iff the word is in the language of the formula.
 */
template <typename ConstraintSymbolT, typename SymbolT, bool state_based>
ATA<ConstraintSymbolT, SymbolT>
translate(const MTLFormula<ConstraintSymbolT> &input_formula,
          std::set<AtomicProposition<SymbolT>> input_alphabet)
{
	const auto formula = input_formula.to_positive_normal_form();
	if constexpr (state_based) {
		if (input_alphabet.empty()) {
			input_alphabet = compute_alphabet<true>(formula.get_alphabet());
		}
		if (input_alphabet.count(AtomicProposition<SymbolT>{{get_l0<ConstraintSymbolT>().ap_}}) > 0) {
			throw std::invalid_argument(
			  fmt::format("The formula alphabet must not contain the symbol '{{{}}}'",
			              get_l0<ConstraintSymbolT>()));
		}
		if (input_alphabet.count(AtomicProposition<SymbolT>{{get_sink<ConstraintSymbolT>().ap_}}) > 0) {
			throw std::invalid_argument(
			  fmt::format("The formula alphabet must not contain the symbol '{{{}}}'",
			              get_sink<ConstraintSymbolT>()));
		}
	} else {
		if (input_alphabet.empty()) {
			// The ATA alphabet is the same as the formula alphabet.
			input_alphabet = formula.get_alphabet();
		}
		if (input_alphabet.count(get_l0<ConstraintSymbolT>()) > 0) {
			throw std::invalid_argument(
			  fmt::format("The formula alphabet must not contain the symbol '{}'",
			              get_l0<ConstraintSymbolT>()));
		}
		if (input_alphabet.count(get_sink<ConstraintSymbolT>()) > 0) {
			throw std::invalid_argument(
			  fmt::format("The formula alphabet must not contain the symbol '{}'",
			              get_sink<ConstraintSymbolT>()));
		}
	}
	const auto alphabet = input_alphabet;
	// const auto alphabet = compute_alphabet<state_based, ConstraintSymbolT>(input_alphabet);
	// S = cl(phi) U {l0}
	auto locations = get_closure(formula);
	locations.insert(get_l0<ConstraintSymbolT>());
	const auto untils              = formula.get_subformulas_of_type(LOP::LUNTIL);
	const auto dual_untils         = formula.get_subformulas_of_type(LOP::LDUNTIL);
	const auto accepting_locations = dual_untils;
	std::set<T<ConstraintSymbolT, SymbolT>> transitions;
	for (const auto &symbol : alphabet) {
		// Initial transition delta(l0, symbol) -> phi
		transitions.insert(T<ConstraintSymbolT, SymbolT>(
		  get_l0<ConstraintSymbolT>(),
		  symbol,
		  init<ConstraintSymbolT, SymbolT, state_based>(formula, symbol, true)));

		for (const auto &until : untils) {
			auto transition_formula = ata::create_disjunction(
			  // init(phi_2, symbol) AND x \in I
			  ata::create_conjunction(
			    init<ConstraintSymbolT, SymbolT, state_based>(until.get_operands().back(), symbol),
			    create_contains<ConstraintSymbolT>(until.get_interval())),
			  // init(phi_1, symbol) AND (psi_1 \until_I psi_2)
			  //                         \->   == until     <-/
			  ata::create_conjunction(
			    init<ConstraintSymbolT, SymbolT, state_based>(until.get_operands().front(), symbol),
			    std::unique_ptr<Formula<ConstraintSymbolT>>(
			      std::make_unique<LocationFormula<ConstraintSymbolT>>(until))));
			transitions.insert(
			  T<ConstraintSymbolT, SymbolT>(until, symbol, std::move(transition_formula)));
		}
		for (const auto &dual_until : dual_untils) {
			auto transition_formula = ata::create_conjunction(
			  ata::create_disjunction(
			    init<ConstraintSymbolT, SymbolT, state_based>(dual_until.get_operands().back(), symbol),
			    create_negated_contains<ConstraintSymbolT>(dual_until.get_interval())),
			  ata::create_disjunction(
			    init<ConstraintSymbolT, SymbolT, state_based>(dual_until.get_operands().front(), symbol),
			    std::unique_ptr<Formula<ConstraintSymbolT>>(
			      std::make_unique<LocationFormula<ConstraintSymbolT>>(dual_until))));
			transitions.insert(
			  T<ConstraintSymbolT, SymbolT>(dual_until, symbol, std::move(transition_formula)));
		}
	}
	return ATA<ConstraintSymbolT, SymbolT>(alphabet,
	                                       MTLFormula<ConstraintSymbolT>{get_l0<ConstraintSymbolT>()},
	                                       accepting_locations,
	                                       std::move(transitions),
	                                       MTLFormula<ConstraintSymbolT>{
	                                         get_sink<ConstraintSymbolT>()});
}
} // namespace tacos::mtl_ata_translation
