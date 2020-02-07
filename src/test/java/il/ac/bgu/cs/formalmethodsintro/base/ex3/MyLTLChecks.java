package il.ac.bgu.cs.formalmethodsintro.base.ex3;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.AP;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import org.junit.Test;

import java.util.Set;

import static il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL.*;
import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.set;
import static org.junit.Assert.assertEquals;

public class MyLTLChecks {

	FvmFacade fvmFacadeImpl = FvmFacade.get();

	@Test
	public void test() {
		AP<String> a = new AP<>("a");
		AP<String> b = new AP<>("b");


		LTL<String> ltl = until(a, until(b, not(a)));

		Automaton<?, String> aut = fvmFacadeImpl.LTL2NBA(ltl);
		int aa = 7;

	}


}
