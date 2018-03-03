</
  define p: output$=26;
  define q: output$=24;
  define r: output$=22;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>