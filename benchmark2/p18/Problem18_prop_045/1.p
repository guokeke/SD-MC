</
  define p: input$=1;
  define q: input$=4;
  define r: output$=25;
  
  alw(!(p and !q) or (alw(!r);next (q)) or alw(!r))
/>