</
  define p: input$=6;
  define q: input$=2;
  define r: output$=22;
  
  alw(!(p and !q) or (alw(!r);next (q)) or alw(!r))
/>