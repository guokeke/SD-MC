//[](AP(A==1) ==> <>AP(RELEASE==1))
</
define p: lr>0;
define q1: status!=7;
define q2: do_ACCEPT!=1;
alw(p->(som(q1) or som(q2)))
/>
