// [](AP(set != 0) ==> <> AP(unset!= 0))
</
define p: set != 0;
define q: unset != 0;
alw(p -> som(q))
/>