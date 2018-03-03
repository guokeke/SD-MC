</
  define p: output$=25;
  define q: output$=23;
  define r: output$=22;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>