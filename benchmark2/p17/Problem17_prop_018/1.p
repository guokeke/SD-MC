</
  define p: output$=21;
  define q: output$=22;
  define r: output$=23;
  
  alw(!(p and !q) or (alw(!r);next (q)) or alw(!r))
/>