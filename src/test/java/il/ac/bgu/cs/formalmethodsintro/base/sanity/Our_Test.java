package il.ac.bgu.cs.formalmethodsintro.base.sanity;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.TSTestUtils;

import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TSTransition;
import il.ac.bgu.cs.formalmethodsintro.base.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;
import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.IntStream;

import static il.ac.bgu.cs.formalmethodsintro.base.TSTestUtils.APs.*;
import static il.ac.bgu.cs.formalmethodsintro.base.TSTestUtils.APs.R;
import static il.ac.bgu.cs.formalmethodsintro.base.TSTestUtils.Actions.*;
import static il.ac.bgu.cs.formalmethodsintro.base.TSTestUtils.Actions.delta;
import static il.ac.bgu.cs.formalmethodsintro.base.TSTestUtils.States.*;
import static org.junit.Assert.*;
import static org.junit.Assert.assertEquals;

public class Our_Test {

    TransitionSystem<TSTestUtils.States, TSTestUtils.Actions, TSTestUtils.APs> ts;
    TransitionSystem<TSTestUtils.States, TSTestUtils.Actions, TSTestUtils.APs> ts1;
    TransitionSystem<TSTestUtils.States, TSTestUtils.Actions, TSTestUtils.APs> ts2;

    static FvmFacade fvmFacadeImpl = FvmFacade.get();


    public static TransitionSystem<TSTestUtils.States, TSTestUtils.Actions, TSTestUtils.APs> myTS1(String name) {
        System.out.println(name);
        TransitionSystem<TSTestUtils.States, TSTestUtils.Actions, TSTestUtils.APs> ts = new TransitionSystem<>();

        ts.setName("Simple Transition System");

        IntStream.range(0, 2).forEach(i -> {
            ts.addState(TSTestUtils.States.values()[i]);
            ts.addAction(TSTestUtils.Actions.values()[i]);
            ts.addAtomicProposition(TSTestUtils.APs.values()[i]);
        });

        ts.addInitialState(a);

        ts.addTransitionFrom(a).action(alpha).to(b);
        ts.addTransitionFrom(b).action(beta).to(a);

        ts.addToLabel(a, P);
        ts.addToLabel(b, Q);

        return ts;
    }

    public static TransitionSystem<TSTestUtils.States, TSTestUtils.Actions, TSTestUtils.APs> myTS2(String name) {
        System.out.println(name);
        TransitionSystem<TSTestUtils.States, TSTestUtils.Actions, TSTestUtils.APs> ts = new TransitionSystem<>();

        ts.setName("Simple Transition System");

        IntStream.range(2, 4).forEach(i -> {
            ts.addState(TSTestUtils.States.values()[i]);
            ts.addAction(TSTestUtils.Actions.values()[i]);
            ts.addAtomicProposition(TSTestUtils.APs.values()[i]);
        });

        ts.addInitialState(c);
        ts.addTransitionFrom(c).action(gamma).to(d);
        ts.addTransitionFrom(d).action(delta).to(c);

        ts.addToLabel(c, R);
        ts.addToLabel(d, R);
        return ts;
    }

    @Before
    public void before()
    {
        ts = TSTestUtils.simpleTransitionSystem();
        ts1 = myTS1("1");
        ts2 = myTS2("2");

    }

    @Test(timeout = 2000)
    public void testDeterministicAction() throws Exception {
        assertTrue(fvmFacadeImpl.isActionDeterministic(ts));
        ts.addInitialState(TSTestUtils.States.b);
        assertFalse(fvmFacadeImpl.isActionDeterministic(ts));

    }

    @Test(timeout = 2000)
    public void testDeterministicAP() throws Exception {
        assertTrue(fvmFacadeImpl.isAPDeterministic(ts));
        ts.addTransitionFrom(TSTestUtils.States.b).action(TSTestUtils.Actions.alpha).to(TSTestUtils.States.d);
        assertFalse(fvmFacadeImpl.isAPDeterministic(ts));
    }


    @Test(timeout = 2000)
    public void testPost1() throws Exception {
        assertEquals(fvmFacadeImpl.post(ts,TSTestUtils.States.a), new HashSet<>(Arrays.asList(TSTestUtils.States.b)));
        ts.addTransitionFrom(TSTestUtils.States.a).action(TSTestUtils.Actions.alpha).to(TSTestUtils.States.d);
        assertEquals(fvmFacadeImpl.post(ts,TSTestUtils.States.a), new HashSet<>(Arrays.asList(TSTestUtils.States.b, TSTestUtils.States.d )));
    }

    @Test(timeout = 2000)
    public void testPost2() throws Exception {
        assertEquals(fvmFacadeImpl.post(ts,TSTestUtils.States.a, TSTestUtils.Actions.alpha), new HashSet<>(Arrays.asList(TSTestUtils.States.b)));
        assertEquals(fvmFacadeImpl.post(ts,TSTestUtils.States.a, TSTestUtils.Actions.beta), new HashSet<>());
    }

    @Test(timeout = 2000)
    public void testPost3() throws Exception {
        Set<TSTestUtils.States> C = new HashSet<>(Arrays.asList(TSTestUtils.States.a, TSTestUtils.States.b));
        assertEquals(fvmFacadeImpl.post(ts, C), new HashSet<>(Arrays.asList(TSTestUtils.States.b, TSTestUtils.States.c)));
    }

    @Test(timeout = 2000)
    public void testPost4() throws Exception {
        Set<TSTestUtils.States> C = new HashSet<>(Arrays.asList(TSTestUtils.States.a, TSTestUtils.States.b));
        assertEquals(fvmFacadeImpl.post(ts, C, TSTestUtils.Actions.alpha), new HashSet<>(Arrays.asList(TSTestUtils.States.b)));
        assertEquals(fvmFacadeImpl.post(ts, C, TSTestUtils.Actions.beta), new HashSet<>(Arrays.asList(TSTestUtils.States.c)));
    }

    @Test(timeout = 2000)
    public void testPre1() throws Exception {
        assertEquals(fvmFacadeImpl.pre(ts,TSTestUtils.States.a), new HashSet<>(Arrays.asList(TSTestUtils.States.d)));
        ts.addTransitionFrom(TSTestUtils.States.b).action(TSTestUtils.Actions.alpha).to(TSTestUtils.States.a);
        assertEquals(fvmFacadeImpl.pre(ts,TSTestUtils.States.a), new HashSet<>(Arrays.asList(TSTestUtils.States.b, TSTestUtils.States.d )));
    }

    @Test(timeout = 2000)
    public void testPre2() throws Exception {
        assertEquals(fvmFacadeImpl.pre(ts,TSTestUtils.States.a, TSTestUtils.Actions.alpha), new HashSet<>());
        assertEquals(fvmFacadeImpl.pre(ts,TSTestUtils.States.a, TSTestUtils.Actions.delta), new HashSet<>(Arrays.asList(TSTestUtils.States.d)));
    }

    @Test(timeout = 2000)
    public void testPre3() throws Exception {
        Set<TSTestUtils.States> C = new HashSet<>(Arrays.asList(TSTestUtils.States.a, TSTestUtils.States.b));
        assertEquals(fvmFacadeImpl.pre(ts, C), new HashSet<>(Arrays.asList(TSTestUtils.States.d, TSTestUtils.States.a)));
    }

    @Test(timeout = 2000)
    public void testPre4() throws Exception {
        Set<TSTestUtils.States> C = new HashSet<>(Arrays.asList(TSTestUtils.States.a, TSTestUtils.States.b));
        assertEquals(fvmFacadeImpl.pre(ts, C, TSTestUtils.Actions.alpha), new HashSet<>(Arrays.asList(TSTestUtils.States.a)));
        assertEquals(fvmFacadeImpl.pre(ts, C, TSTestUtils.Actions.beta), new HashSet<>());
    }

    @Test(timeout = 2000)
    public void isTerminator() throws Exception {
        assertFalse(fvmFacadeImpl.isStateTerminal(ts,  TSTestUtils.States.a));
        ts.removeTransition(new TSTransition<>(TSTestUtils.States.a, TSTestUtils.Actions.alpha, TSTestUtils.States.b));
        assertTrue(fvmFacadeImpl.isStateTerminal(ts,  TSTestUtils.States.a));
    }



    @Test(timeout = 2000)
    public void testInterleave1() throws Exception {
        TransitionSystem inteleaveTs = fvmFacadeImpl.interleave(ts1, ts2);
        System.out.println(inteleaveTs.getStates());
        assertEquals(inteleaveTs.getInitialStates().toString(), "[<a,c>]");
        assertEquals(inteleaveTs.getActions(), new HashSet<TSTestUtils.Actions>(Arrays.asList(TSTestUtils.Actions.alpha, TSTestUtils.Actions.beta, TSTestUtils.Actions.gamma, TSTestUtils.Actions.delta)));
        assertEquals(inteleaveTs.getAtomicPropositions(), new HashSet<TSTestUtils.APs>(Arrays.asList(TSTestUtils.APs.R, TSTestUtils.APs.P, TSTestUtils.APs.Q, TSTestUtils.APs.S)));

        System.out.println(inteleaveTs.getTransitions());
        System.out.println(inteleaveTs.getAtomicPropositions());
        System.out.println(inteleaveTs.getLabelingFunction());
    }

}
