</
  define p: output$=22;
  define q: output$=23;
  define r: output$=26;
  
  alw(!(p and !q) or (alw(!r);next (q)) or alw(!r))
/>