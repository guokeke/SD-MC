</
  define p: output$=24;
  define q: output$=21;
  define r: output$=26;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)) or alw(!q))
/>