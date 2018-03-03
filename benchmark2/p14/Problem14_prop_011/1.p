</
  define p: output$=26;
  define q: output$=24;
  define r: output$=23;
  
  alw(!(p and !q) or (alw(!q);next (r and !q)) or alw(!q))
/>