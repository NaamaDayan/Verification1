package il.ac.bgu.cs.formalmethodsintro.base.ex3;

import static il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL.and;
import static il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL.next;
import static il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL.not;
import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.set;
import static org.junit.Assert.assertEquals;

import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.AP;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;

public class LTLTest {

	FvmFacade fvmFacadeImpl = FvmFacade.get();

	@Test
	public void test() {
		AP<String> p = new AP<>("p");

		LTL<String> ltl = and(not(p), next(p));

		Automaton<?, String> aut = fvmFacadeImpl.LTL2NBA(ltl);
		Automaton<?, String> exp = expected();


		assertEquals(aut, exp);
	}

	Automaton<Pair<Set<String>, Integer>, String> expected() {
		Automaton<Pair<Set<String>, Integer>, String> aut = new Automaton<>();

		Pair<Set<String>, Integer> p_np = new Pair<>(set("!(!p /\\ ()p)", "()p", "p"), 0);
		Pair<Set<String>, Integer> p_notnp = new Pair<>(set("!(!p /\\ ()p)", "!()p", "p"), 0);
		Pair<Set<String>, Integer> notp_np = new Pair<>(set("(!p /\\ ()p)", "!p", "()p"), 0);
		Pair<Set<String>, Integer> notp_notnp = new Pair<>(set("!(!p /\\ ()p)", "!()p", "!p"), 0);

		Set<String> p = set("p");
		Set<String> notp = set();

		aut.addTransition(notp_notnp, notp, notp_np);
		aut.addTransition(notp_notnp, notp, notp_notnp);
		aut.addTransition(p_notnp, p, notp_notnp);
		aut.addTransition(p_notnp, p, notp_np);
		aut.addTransition(notp_np, notp, p_np);
		aut.addTransition(notp_np, notp, p_notnp);
		aut.addTransition(p_np, p, p_np);
		aut.addTransition(p_np, p, p_notnp);

		aut.setInitial(notp_np);

		aut.setAccepting(p_np);
		aut.setAccepting(p_notnp);
		aut.setAccepting(notp_np);
		aut.setAccepting(notp_notnp);

		return aut;

	}

}
