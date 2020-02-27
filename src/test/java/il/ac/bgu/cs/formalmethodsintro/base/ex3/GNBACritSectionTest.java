package il.ac.bgu.cs.formalmethodsintro.base.ex3;

import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.set;
import static java.util.Arrays.asList;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.sql.SQLOutput;
import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.util.Util;

public class GNBACritSectionTest {
	FvmFacade fvmFacadeImpl = FvmFacade.get();

	@Test
	public void simpleTest() throws Exception {

		MultiColorAutomaton<String, String> mulAut = getMCAut();
		Automaton<?, String> aut = fvmFacadeImpl.GNBA2NBA(mulAut);
		Automaton<String, String> expected = getExpected();
		assertEquals(expected, aut);

	}

	MultiColorAutomaton<String, String> getMCAut() {
		MultiColorAutomaton<String, String> aut = new MultiColorAutomaton<>();

		aut.addTransition("s0", set("crit2"), "s2");
		aut.addTransition("s0", set("crit1"), "s1");

		// True transitions
		for (Set<String> s : Util.powerSet(set("crit1", "crit2"))) {
			aut.addTransition("s0", new HashSet<>(s), "s0");
			aut.addTransition("s1", new HashSet<>(s), "s0");
			aut.addTransition("s2", new HashSet<>(s), "s0");
		}

		aut.setInitial("s0");
		aut.setAccepting("s1", 0);
		aut.setAccepting("s2", 1);

		return aut;
	}

	Automaton<String, String> getExpected() {
		Automaton<String, String> aut = new Automaton<>();

		Set<String> none = set();
		Set<String> crit1 = set("crit1");
		Set<String> crit2 = set("crit2");
		Set<String> both = set("crit2", "crit1");

		aut.addTransition("s01", crit2, "s21");
		aut.addTransition("s01", crit1, "s11");
		aut.addTransition("s02", crit2, "s22");
		aut.addTransition("s02", crit1, "s12");

		// True transitions
		for (Set<String> s : asList(none, crit1, crit2, both)) {
			aut.addTransition("s01", s, "s01");
			aut.addTransition("s11", s, "s02");
			aut.addTransition("s02", s, "s02");
			aut.addTransition("s21", s, "s01");
			aut.addTransition("s12", s, "s02");
			aut.addTransition("s22", s, "s01");
		}

		aut.setInitial("s01");

		aut.setAccepting("s11");

		return aut;
	}

}
