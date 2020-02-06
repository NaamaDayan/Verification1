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
		AP<String> p = new AP<>("a");

		LTL<String> ltl = next(p);

		Automaton<?, String> aut = fvmFacadeImpl.LTL2NBA(ltl);

	}


}
