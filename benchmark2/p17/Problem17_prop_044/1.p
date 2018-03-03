</
  define p: output$=25;
  define q: output$=26;
  define r: output$=22;
  
  alw(!(p and !q) or (alw(!r);next (q)) or alw(!r))
/>