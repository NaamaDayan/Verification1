package il.ac.bgu.cs.formalmethodsintro.base.ex3;

import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.p;
import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.set;
import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.transition;
import static org.junit.Assert.assertEquals;

import java.util.Collections;
import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;

public class AutTsProductTests2 {
	FvmFacade fvmFacadeImpl = FvmFacade.get();

	@SuppressWarnings("unchecked")
	@Test
	public void autTimesTs() {
		TransitionSystem<String, String, String> ts = buildTransitionSystem();
		Automaton<String, String> aut = buildAutomaton();

		TransitionSystem<Pair<String, String>, String, String> comb = fvmFacadeImpl.product(ts, aut);

		assertEquals(set(p("green", "q0")), comb.getInitialStates());
		assertEquals(set("switch"), comb.getActions());
		assertEquals(set("q1", "q0"), comb.getAtomicPropositions());
		assertEquals(set(transition(p("green", "q0"), "switch", p("yellow", "q1")), transition(p("red/yellow", "q0"), "switch", p("green", "q0")), transition(p("yellow", "q1"), "switch", p("red", "q0")), transition(p("red", "q0"), "switch", p("red/yellow", "q0"))), comb.getTransitions());
		assertEquals(set("q0"), comb.getLabel(p("red", "q0")));
		assertEquals(set("q0"), comb.getLabel(p("green", "q0")));
		assertEquals(set("q1"), comb.getLabel(p("yellow", "q1")));
		assertEquals(set("q0"), comb.getLabel(p("red/yellow", "q0")));

	}

	private Automaton<String, String> buildAutomaton() {
		Automaton<String, String> aut = new Automaton<>();

		String q0 = "q0";
		String q1 = "q1";
		String qf = "qF";

		Set<String> notRedAndNotYellow = Collections.emptySet();
		Set<String> redAndNotYellow = set("red");
		Set<String> yellowAndNotRed = set("yellow");
		Set<String> redAndYellow = set("red", "yellow");

		aut.addTransition(q0, notRedAndNotYellow, q0);
		aut.addTransition(q0, yellowAndNotRed, q1);
		aut.addTransition(q0, redAndNotYellow, qf);
		aut.addTransition(q0, redAndYellow, qf);

		aut.addTransition(q1, yellowAndNotRed, q1);
		aut.addTransition(q1, redAndYellow, q1);
		aut.addTransition(q1, redAndNotYellow, q0);
		aut.addTransition(q1, notRedAndNotYellow, q0);

		aut.addTransition(qf, notRedAndNotYellow, qf);
		aut.addTransition(qf, redAndNotYellow, qf);
		aut.addTransition(qf, yellowAndNotRed, qf);
		aut.addTransition(qf, redAndYellow, qf);

		aut.setInitial(q0);
		aut.setAccepting(qf);
		return aut;
	}

	private TransitionSystem<String, String, String> buildTransitionSystem() {
		TransitionSystem<String, String, String> ts = new TransitionSystem<>();

		String gr = "green";
		String yl = "yellow";
		String rd = "red";
		String ry = "red/yellow";

		ts.addState(gr);
		ts.addState(yl);
		ts.addState(rd);
		ts.addState(ry);
		ts.addInitialState(gr);

		String sw = "switch";
		ts.addAction(sw);

		ts.addTransition(new TSTransition<>(gr, sw, yl));
		ts.addTransition(new TSTransition<>(yl, sw, rd));
		ts.addTransition(new TSTransition<>(rd, sw, ry));
		ts.addTransition(new TSTransition<>(ry, sw, gr));

		ts.addAtomicProposition("yellow");
		ts.addAtomicProposition("red");

		ts.addToLabel(yl, "yellow");
		ts.addToLabel(rd, "red");
		return ts;
	}

}