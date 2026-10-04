// Entry point of dialysis-paper3.jar. Settings are environment variables, exactly as in the test harness
// (see scripts/xeon/README.md).
//   java -jar dialysis-paper3.jar series              algebraic solver on one family   (FAMILY, DIR, OUT, ...)
//   java -jar dialysis-paper3.jar chain               stabiliser chain on instances    (SC_FILES, OUT, ...)
//   java -jar dialysis-paper3.jar oracle              Traces on one instance (TR_FILE, TR_COLOUR=none|pi, OUT)
//   java -jar dialysis-paper3.jar traces --family=<f> --out=<csv> --timeoutMs=<ms>
//                                                    uncoloured Traces baseline / oracle, one process per instance
//   java -jar dialysis-paper3.jar run <Class> <method> any no-argument experiment method
public class Paper3Main {
    public static void main(String[] a) throws Exception {
        String cls, method;
        String cmd = a.length == 0 ? "" : a[0];
        if (cmd.equals("traces")) {   // separate oracle job (dialysis.groupdiscovery.TracesBaselineRunner, main code)
            Class.forName("dialysis.groupdiscovery.TracesBaselineRunnerKt").getMethod("main", String[].class)
                .invoke(null, (Object) java.util.Arrays.copyOfRange(a, 1, a.length));
            return;
        }
        switch (cmd) {
            case "series": cls = "dialysis.experimental.DecompositionCanonicalFormsTest"; method = "parityCampaign"; break;
            case "chain":  cls = "dialysis.experimental.PieceProfileTest"; method = "stabiliserChain"; break;
            case "oracle": cls = "dialysis.experimental.TracesOracle"; method = "tracesOne"; break;
            case "run":
                if (a.length < 3) { usage(); return; }
                cls = a[1]; method = a[2]; break;
            default: usage(); return;
        }
        Class<?> c = Class.forName(cls);
        Object o = c.getDeclaredConstructor().newInstance();
        try { c.getMethod(method).invoke(o); }
        catch (java.lang.reflect.InvocationTargetException e) { e.getCause().printStackTrace(); System.exit(1); }
        System.exit(0);
    }
    private static void usage() {
        System.err.println("usage: java -jar dialysis-paper3.jar series | chain | oracle | traces ... | run <Class> <method>   (settings: environment, see README)");
        System.exit(2);
    }
}
