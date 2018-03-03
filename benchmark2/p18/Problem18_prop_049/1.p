</
  define p: input$=3;
  define q: input$=4;
  define r: output$=26;
  
  alw(!(p and !q) or (alw(!r);next (q)) or alw(!r))
/>
