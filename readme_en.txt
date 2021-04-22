This program is made for fast evaluation of flight batteries under real load.

This requires an entire flight with a fully charged battery. The assessment is (and can be) only very superficial and is dependent on or influenced by many factors. Nevertheless, it can be seen intuitively, at least on the diagram, how the discharge behavior of the battery is. The advantage over pure voltage measurement is that you can see the voltage curve under load. If the voltage drops sharply under load, this indicates a high internal resistance of the battery. This happens gradually with aging or relatively quickly with defects.
In any case, it is questionable to fly batteries that can no longer be fully trusted. Therefore I consider a constant observation of the batteries necessary (post-flight-check).
This tool should simplify that.

To see the voltage history, you have to load the telemetry data from the flight. This can be TLOG files, telemetry CSV files or the corresponding pedants at Mantis Q or Breeze. The program can handle all common telemetry data from Yuneec copters, as well as from the Blade Chroma or 350QX (if they are controlled with the ST10).

In the attached screenshot we see the evaluation of a TLOG file from the H520, which contains three flights with three different batteries, here called segments of the file.
Segment 1 shows the typical course of a good battrie with long flight time and low voltage dip.
Segment 2 shows an aged battery, which should be inspected continuously.
Segment 3 shows a defective or at least very old battery that belongs in the scrap. This battery actually caused a crash.
