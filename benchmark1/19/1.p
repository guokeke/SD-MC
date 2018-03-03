//[](AP(A==1) ==> <>AP(RELEASE==1))
</
define p: lock = 1;
define q: lock = 0;
alw(p->som(q))
/>
