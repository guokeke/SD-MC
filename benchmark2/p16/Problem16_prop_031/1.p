</
  define p: output$=23;
  define q: input$=4;
  define r: output$=22;
  
  alw(!(p and !q) or (alw(!r);next (q)) or alw(!r))
/>