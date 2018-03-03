</
  define p: output$=24;
  define q: output$=25;
  define r: output$=22;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>
