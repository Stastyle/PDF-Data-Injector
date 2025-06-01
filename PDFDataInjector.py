## PDFDataInjector.py
# A Tkinter application to inject data from an Excel file into a PDF template.
# It allows users to select a PDF template, an Excel data file, and an output directory,
# and dynamically place text fields on the PDF based on the Excel data.
# The application supports zooming, panning, and RTL text handling for Hebrew text.
# It also provides a preview of the PDF with the injected data.
# and _on_canvas_b1_motion.
# UI_LANGUAGE: English. All user-facing strings should be in English.
# If a marker was being dragged, it will be handled by the marker's own bindings.
# version number should be increased with each generated iteration by 0.01.
# version 1.22

import tkinter as tk
from tkinter import filedialog, messagebox, font as tkFont, simpledialog, ttk
import pandas as pd
import fitz  # PyMuPDF
import os
import arabic_reshaper
from bidi.algorithm import get_display
import matplotlib.font_manager as fm # Added for finding font file paths
from PIL import Image, ImageTk # For signature image handling

# Define marker colors for dynamic text fields
MARKER_COLORS = ["red", "blue", "green", "purple", "orange", "cyan", "magenta", "brown", "pink", "olive"]

# Class constants
DEFAULT_SIGNATURE_WIDTH_PT = 72  # Default width for a new signature (1 inch)
Y_OFFSET_PDF_OUTPUT = 2  # Small Y offset adjustment for PDF output, in points
TKINTER_FONT_SCALE_FACTOR = 0.85 # Adjust this factor as needed for Tkinter's font rendering vs PDF
RESIZE_HANDLE_SIZE = 8 # pixels
RESIZE_HANDLE_OFFSET = RESIZE_HANDLE_SIZE // 2
RESIZE_HANDLE_TAG = "resize_handle"
RESIZE_HANDLE_COLOR = "gray" # Color for handles
RESIZE_HANDLE_ACTIVE_COLOR = "blue" # Color when mouse is over a handle
DEFAULT_PDF_TEXT_COLOR = (0, 0, 0) # Black

class PDFBatchApp:
    def __init__(self, master):
        self.master = master
        master.title("PDF Data Injector")
        master.geometry("950x800") # Increased height for preview

        # --- Variables ---
        self.pdf_path = tk.StringVar()
        self.excel_path = tk.StringVar()
        self.output_dir = tk.StringVar()
        # StringVars for displaying only filenames/directory names
        self.pdf_display_var = tk.StringVar(value="(No file selected)")
        self.excel_display_var = tk.StringVar(value="(No file selected)")
        self.output_dir_display_var = tk.StringVar(value="(No folder selected)")
        self.font_family_var = tk.StringVar() 
        self.font_size_var = tk.IntVar(value=12)     # Default font size
        self.excel_preview_text = tk.StringVar(value="Excel Preview: (Load Excel file)") # For internal data, not displayed directly
        self.current_zoom_factor = tk.DoubleVar(value=1.0)
        self.zoom_display_var = tk.StringVar(value="Zoom: 100%")
        self.preview_row_index = tk.IntVar(value=0) # 0-based index for preview row
        
        # --- PDF Page Navigation Variables ---
        self.current_pdf_page_num = tk.IntVar(value=0)
        self.pdf_total_pages = tk.IntVar(value=0)
        self.pdf_page_display_var = tk.StringVar(value="Page: -/-")
        self.preview_row_display = tk.StringVar(value="Row: -")
        
        self.is_rtl_vars = [] # List of tk.BooleanVar for RTL status of each column
        self.col_status_vars = [] # List of tk.StringVar for V/X status of each column

        # --- Signature Mode Variables ---
        self.signature_mode_active = tk.BooleanVar(value=False)
        self.loaded_signature_pil_images = [] # List of (PIL.Image, image_path, display_name)
        self.placed_signatures_data = [] # List of dicts for each placed signature instance
        # Each dict: {'pil_image_idx': int, 'pdf_rect_pts': fitz.Rect, 'tk_photo': ImageTk.PhotoImage, 
        #             'canvas_item_id': int, 'selected': False, 'aspect_ratio': float}
        self.active_signature_pil_idx_to_place = tk.IntVar(value=-1) # Index in self.loaded_signature_pil_images
        self.selected_placed_signature_idx = tk.IntVar(value=-1) # Index in self.placed_signatures_data
        # self.signature_width_var = tk.DoubleVar(value=DEFAULT_SIGNATURE_WIDTH_PT) # Removed for drag-resize
        # self.signature_height_var = tk.DoubleVar(value=0) # Removed for drag-resize

        self._bind_variables() # Renamed from _bind_font_variables

        self.pdf_doc = None
        self.pdf_page_width_pt = 0
        self.pdf_page_height_pt = 0
        self.image_on_canvas_width_px = 0
        self.image_on_canvas_height_px = 0

        self.photo_image = None # To prevent garbage collection
        self.coords_pdf = [] # List to store PDF coordinates for each text field
        self.active_coord_to_set_idx = None # Index of the coordinate currently being set by click
        self.excel_data_preview = None
        self.num_excel_cols = 0 # Number of columns detected in Excel, determines number of text fields
        self.preview_text_items = [] # Store IDs of preview text items on canvas
        self.is_text_preview_active = True # Default to text preview being active
        self._drag_data = {"x": 0, "y": 0, "item": None, "col_idx": None} # For dragging markers
        self._item_drag_active = False # New flag: True if a marker or signature is being dragged
        # self._pan_data = {"x": 0, "y": 0, "active": False} # Old, for Button-3 panning
        self._pan_data = {
            "press_x": 0, "press_y": 0,  # Coords of initial B1 press on canvas
            "is_potential_pan_or_click": False,  # True after B1 press on canvas (not on marker)
            "has_dragged_for_pan": False,  # True if mouse moved enough during B1 hold
            "pan_threshold": 5  # pixels, adjust as needed
        }
        self._resize_data = {
            "active": False,
            "sig_idx": -1,
            "handle_type": None, # e.g., "tl", "tr", "br", "bl"
            "start_mouse_x_canvas": 0, # Canvas coords
            "start_mouse_y_canvas": 0, # Canvas coords
            "original_pdf_rect": None, # fitz.Rect of the signature at drag start (PDF points, y from top)
            "canvas_item_id_sig": None, 
            "aspect_ratio": 1.0
        }

        # --- GUI Layout ---
        # Main application frame
        main_app_frame = tk.Frame(master)
        main_app_frame.pack(fill=tk.BOTH, expand=True)
        self.main_app_frame = main_app_frame # Store for later use if needed

        # Frame for file selection and controls
        controls_frame = tk.Frame(main_app_frame, padx=10, pady=10)
        controls_frame.pack(side=tk.TOP, fill=tk.X, padx=5, pady=5)

        # Content area for canvas and sidebar
        content_area_frame = tk.Frame(main_app_frame)
        content_area_frame.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=5, pady=(0,5))

        # --- Text Injection Controls (will be hidden in signature mode) ---
        # PDF Selection
        tk.Label(controls_frame, text="PDF Template:").grid(row=0, column=0, sticky="e", padx=5, pady=2)
        tk.Button(controls_frame, text="Select PDF", command=self.load_pdf_template, width=12).grid(row=0, column=1, padx=5, pady=2, sticky="e")
        tk.Entry(controls_frame, textvariable=self.pdf_display_var, width=40, state="readonly").grid(row=0, column=2, padx=5, pady=2, sticky="ew")

        # Excel Selection
        tk.Label(controls_frame, text="Excel Data File:").grid(row=1, column=0, sticky="e", padx=5, pady=2)
        tk.Button(controls_frame, text="Select Excel", command=self.load_excel_data, width=12).grid(row=1, column=1, padx=5, pady=2, sticky="e")
        tk.Entry(controls_frame, textvariable=self.excel_display_var, width=40, state="readonly").grid(row=1, column=2, padx=5, pady=2, sticky="ew")

        # Output Directory Selection
        tk.Label(controls_frame, text="Output Folder:").grid(row=2, column=0, sticky="e", padx=5, pady=2)
        tk.Button(controls_frame, text="Select Folder", command=self.select_output_dir, width=12).grid(row=2, column=1, padx=5, pady=2, sticky="e")
        tk.Entry(controls_frame, textvariable=self.output_dir_display_var, width=40, state="readonly").grid(row=2, column=2, padx=5, pady=2, sticky="ew")

        # Font Selection
        tk.Label(controls_frame, text="Font Family:").grid(row=3, column=0, sticky="e", padx=5, pady=2)
        font_details_frame = tk.Frame(controls_frame)
        font_details_frame.grid(row=3, column=1, columnspan=2, sticky="e", padx=5, pady=2) 
        
        # Populate font families
        font_families = sorted(list(tkFont.families()))
        self.font_combo = ttk.Combobox(font_details_frame, textvariable=self.font_family_var, values=font_families, width=23, state="readonly")
        if "Arial" in font_families:
            self.font_family_var.set("Arial") # Default font
        elif font_families:
            self.font_family_var.set(font_families[0]) # Fallback to first available font
        self.font_combo.pack(side=tk.LEFT)

        tk.Label(font_details_frame, text="Size:").pack(side=tk.LEFT, padx=(10, 2))
        tk.Entry(font_details_frame, textvariable=self.font_size_var, width=5).pack(side=tk.LEFT)

        # Zoom controls and Text Preview Button
        zoom_preview_frame = tk.Frame(controls_frame)
        zoom_preview_frame.grid(row=4, column=0, columnspan=3, sticky="e", pady=5) # Adjusted row
        tk.Button(zoom_preview_frame, text="-", command=lambda: self.zoom(-0.2)).pack(side=tk.LEFT, padx=2)
        tk.Label(zoom_preview_frame, textvariable=self.zoom_display_var).pack(side=tk.LEFT, padx=5)
        tk.Button(zoom_preview_frame, text="+", command=lambda: self.zoom(0.2)).pack(side=tk.LEFT, padx=2)
        
        # Preview Row Controls
        self.prev_row_button = tk.Button(zoom_preview_frame, text="↑", command=lambda: self._change_preview_row(-1), state=tk.DISABLED, width=2)
        self.prev_row_button.pack(side=tk.LEFT, padx=(15,0)) 

        self.preview_row_label = tk.Label(zoom_preview_frame, textvariable=self.preview_row_display, width=8)
        self.preview_row_label.pack(side=tk.LEFT, padx=2)

        self.next_row_button = tk.Button(zoom_preview_frame, text="↓", command=lambda: self._change_preview_row(1), state=tk.DISABLED, width=2)
        self.next_row_button.pack(side=tk.LEFT, padx=(0,5))

        self.toggle_text_preview_button = tk.Button(zoom_preview_frame, text="Show/Hide Preview", command=self.toggle_text_preview)
        self.toggle_text_preview_button.pack(side=tk.LEFT, padx=(10,0))
        # "Generate current PDF" button moved below

        # Generate Buttons Frame (for main generate and current generate)
        generate_buttons_frame = tk.Frame(controls_frame)
        generate_buttons_frame.grid(row=5, column=0, columnspan=3, sticky="e", pady=10)

        self.generate_all_pdfs_button = tk.Button(generate_buttons_frame, text="Generate PDF Files", command=self.generate_output_pdfs, bg="lightblue", font=("Arial", 12, "bold"))
        self.generate_all_pdfs_button.pack(side=tk.RIGHT, padx=(5,0)) 

        self.generate_current_pdf_button = tk.Button(generate_buttons_frame, text="Generate Current PDF", command=self.generate_single_preview_pdf)
        self.generate_current_pdf_button.pack(side=tk.RIGHT)

        # Store references to text-injection specific control groups for easy hide/show
        self.text_injection_controls_row0 = [controls_frame.grid_slaves(row=0, column=c)[0] for c in range(3) if controls_frame.grid_slaves(row=0, column=c)]
        self.text_injection_controls_row1 = [controls_frame.grid_slaves(row=1, column=c)[0] for c in range(3) if controls_frame.grid_slaves(row=1, column=c)]
        self.text_injection_controls_row2 = [controls_frame.grid_slaves(row=2, column=c)[0] for c in range(3) if controls_frame.grid_slaves(row=2, column=c)] # Output folder might be shared
        self.text_injection_controls_row3 = [controls_frame.grid_slaves(row=3, column=c)[0] for c in range(3) if controls_frame.grid_slaves(row=3, column=c)]
        # Row 4 (zoom/preview) is shared. Row 5 (generate buttons) is handled separately.

        # --- Signature Mode Controls (initially hidden, placed in controls_frame) ---
        self.signature_controls_frame = tk.Frame(controls_frame)
        # This frame is no longer used for primary signature controls, they are now in the sidebar.
        # The "Delete Selected Signature" button is now built dynamically in the sidebar.
        
        self.signature_mode_active.trace_add("write", self._on_signature_mode_change)

        # PDF Page Navigation Frame (below content_area, above status_label)
        self.pdf_nav_frame = tk.Frame(main_app_frame)
        # This frame will be packed later, only if a PDF is loaded.
        self.prev_pdf_page_button = tk.Button(self.pdf_nav_frame, text="< Prev Page", command=lambda: self._change_pdf_page(-1), state=tk.DISABLED)
        self.prev_pdf_page_button.pack(side=tk.LEFT, padx=5, pady=2)
        self.pdf_page_label = tk.Label(self.pdf_nav_frame, textvariable=self.pdf_page_display_var, width=15)
        self.pdf_page_label.pack(side=tk.LEFT, padx=5, pady=2)
        self.next_pdf_page_button = tk.Button(self.pdf_nav_frame, text="Next Page >", command=lambda: self._change_pdf_page(1), state=tk.DISABLED)
        self.next_pdf_page_button.pack(side=tk.LEFT, padx=5, pady=2)


        # Status Label
        self.status_label = tk.Label(main_app_frame, text="Please load a PDF template to begin.", bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.status_label.pack(side=tk.BOTTOM, fill=tk.X)
        # Pack pdf_nav_frame *before* status_label so it's above
        self.pdf_nav_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(0,2))
        self.pdf_nav_frame.pack_forget() # Initially hidden

        # Canvas for PDF Preview
        self.canvas_container = tk.Frame(content_area_frame, bd=2, relief=tk.SUNKEN)
        self.canvas_container.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0,5))

        # Sidebar for dynamic column controls
        self.column_controls_sidebar = tk.Frame(content_area_frame, width=200, bd=1, relief=tk.RAISED)
        self.column_controls_sidebar.pack(side=tk.RIGHT, fill=tk.Y, padx=(5,0))
        self.canvas = tk.Canvas(self.canvas_container, bg="lightgrey") # Changed bg for better visibility

        self.h_scrollbar = tk.Scrollbar(self.canvas_container, orient=tk.HORIZONTAL, command=self.canvas.xview)
        self.v_scrollbar = tk.Scrollbar(self.canvas_container, orient=tk.VERTICAL, command=self.canvas.yview)
        self.canvas.configure(xscrollcommand=self.h_scrollbar.set, yscrollcommand=self.v_scrollbar.set)

        self.h_scrollbar.pack(side=tk.BOTTOM, fill=tk.X)
        self.v_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # self.canvas.bind("<Button-1>", self.handle_canvas_click) # Replaced by specific B1 bindings
        self.canvas.bind("<ButtonPress-1>", self._on_canvas_b1_press)
        self.canvas.bind("<B1-Motion>", self._on_canvas_b1_motion)
        self.canvas.bind("<ButtonRelease-1>", self._on_canvas_b1_release)

        # Bindings for dragging markers
        self.canvas.tag_bind("marker", "<ButtonPress-1>", self.on_marker_press)
        self.canvas.tag_bind("marker", "<B1-Motion>", self.on_marker_motion)
        self.canvas.tag_bind("marker", "<ButtonRelease-1>", self.on_marker_release)
        self.canvas.tag_bind("marker", "<Double-Button-1>", self.on_marker_double_click)
        
        self.canvas.tag_bind("signature_instance", "<ButtonPress-1>", self.on_placed_signature_press)
        self.canvas.tag_bind("signature_instance", "<B1-Motion>", self.on_placed_signature_motion)
        self.canvas.tag_bind("signature_instance", "<ButtonRelease-1>", self.on_placed_signature_release)

        # Bindings for resize handles
        self.canvas.tag_bind(RESIZE_HANDLE_TAG, "<Enter>", self._on_resize_handle_enter)
        self.canvas.tag_bind(RESIZE_HANDLE_TAG, "<Leave>", self._on_resize_handle_leave)
        self.canvas.tag_bind(RESIZE_HANDLE_TAG, "<ButtonPress-1>", self._on_resize_handle_press)
        # Motion and Release for resize handles will be managed by the global canvas bindings when _resize_data["active"] is true

        # Bindings for mouse wheel zoom
        self.canvas.bind("<MouseWheel>", self._handle_mouse_wheel_zoom)  # Windows & MacOS
        self.canvas.bind("<Button-4>", self._handle_mouse_wheel_zoom)    # Linux scroll up
        self.canvas.bind("<Button-5>", self._handle_mouse_wheel_zoom)    # Linux scroll down
        master.bind("<Delete>", self._on_delete_key_press) # Bind Delete key to the master window

        # Initially hide mode-specific controls until a PDF is loaded
        # Excel controls (row 1)
        for widget in self.text_injection_controls_row1:
            widget.grid_remove()
        # Output folder controls (row 2)
        for widget in self.text_injection_controls_row2:
            widget.grid_remove()
        # Font controls (row 3)
        for widget in self.text_injection_controls_row3:
            widget.grid_remove()

        # Text-specific parts of zoom_preview_frame
        self.prev_row_button.pack_forget()
        self.preview_row_label.pack_forget()
        self.next_row_button.pack_forget()
        self.toggle_text_preview_button.pack_forget()
        # Text-specific generate button
        self.generate_all_pdfs_button.pack_forget()
        # The generate_current_pdf_button's text and command will be set by _on_signature_mode_change
        # The column_controls_sidebar content is built by _build_dynamic_coord_controls, called by _on_signature_mode_change.

    def _on_signature_mode_change(self, *args):
        is_sig_mode = self.signature_mode_active.get()
        if is_sig_mode:
            self.status_label.config(text="Signature mode active. Load a signature image and place it on the document.")
            # Hide text injection controls
            for widget_list in [self.text_injection_controls_row1,  # Excel
                                self.text_injection_controls_row2,  # Output Folder
                                self.text_injection_controls_row3]: # Font
                for widget in widget_list:
                    widget.grid_remove()
            self.column_controls_sidebar.pack_forget() # Hide column sidebar
            self.generate_all_pdfs_button.pack_forget() # Hide batch generate
            self.generate_current_pdf_button.config(text="Create Signed PDF", command=self.generate_signed_pdf)
            
            # Ensure text-specific preview controls are hidden
            self.prev_row_button.pack_forget()
            self.preview_row_label.pack_forget()
            self.next_row_button.pack_forget()
            self.toggle_text_preview_button.pack_forget()
            
            self.signature_controls_frame.grid_remove() # Ensure the old frame for delete button is hidden
            
            # Clear text-related previews and data
            self.excel_data_preview = None
            self.coords_pdf = []
            self.num_excel_cols = 0
            self._update_text_preview() # Clears text preview
            self._draw_markers() # Clears markers
            self.excel_display_var.set("(N/A in Signature Mode)")
            self.column_controls_sidebar.pack(side=tk.RIGHT, fill=tk.Y, padx=(5,0)) # Ensure sidebar is visible

        else: # Text injection mode
            self.status_label.config(text="Text injection mode. Load PDF, Excel and define positions.")
            # Show text injection controls
            # Row 1: Excel
            for col_idx, widget in enumerate(self.text_injection_controls_row1):
                if col_idx == 0: widget.grid(row=1, column=0, sticky="e", padx=5, pady=2) # Label
                elif col_idx == 1: widget.grid(row=1, column=1, padx=5, pady=2, sticky="e") # Button
                elif col_idx == 2: widget.grid(row=1, column=2, padx=5, pady=2, sticky="ew") # Entry
            # Row 2: Output Folder
            for col_idx, widget in enumerate(self.text_injection_controls_row2):
                if col_idx == 0: widget.grid(row=2, column=0, sticky="e", padx=5, pady=2) # Label
                elif col_idx == 1: widget.grid(row=2, column=1, padx=5, pady=2, sticky="e") # Button
                elif col_idx == 2: widget.grid(row=2, column=2, padx=5, pady=2, sticky="ew") # Entry
            # Row 3: Font
            for col_idx, widget in enumerate(self.text_injection_controls_row3):
                if col_idx == 0: widget.grid(row=3, column=0, sticky="e", padx=5, pady=2) # Label
                elif col_idx == 1: widget.grid(row=3, column=1, columnspan=2, sticky="e", padx=5, pady=2) # font_details_frame
            self.column_controls_sidebar.pack(side=tk.RIGHT, fill=tk.Y, padx=(5,0)) # Show column sidebar
            self.generate_all_pdfs_button.pack(side=tk.RIGHT, padx=(5,0))
            self.generate_current_pdf_button.config(text="Generate Current PDF", command=self.generate_single_preview_pdf)

            # Ensure text-specific preview controls are visible
            self.prev_row_button.pack(side=tk.LEFT, padx=(15,0))
            self.preview_row_label.pack(side=tk.LEFT, padx=2)
            self.next_row_button.pack(side=tk.LEFT, padx=(0,5))
            self.toggle_text_preview_button.pack(side=tk.LEFT, padx=(10,0))
            
            self.signature_controls_frame.grid_remove() 
            # Clear signature data
            self.loaded_signature_pil_images = []
            self.placed_signatures_data = []
            self.active_signature_pil_idx_to_place.set(-1)
            self.selected_placed_signature_idx.set(-1)
            self._draw_placed_signatures() # Clears signature previews
            if self.pdf_doc: # If PDF is loaded, ensure page nav is visible
                self._redisplay_pdf_page() 
        self._build_dynamic_coord_controls() # Rebuild sidebar for the current mode
    def _bind_variables(self): # Renamed
        self.font_family_var.trace_add("write", self._on_font_change)
        self.font_size_var.trace_add("write", self._on_font_change)

    def _build_dynamic_coord_controls(self):
        # Clear existing controls
        for widget in self.column_controls_sidebar.winfo_children():
            widget.destroy()
        
        self.is_rtl_vars = []
        self.col_status_vars = []

        if self.signature_mode_active.get():
            # --- Section 1: Load New Signature Button ---
            load_button_frame = tk.Frame(self.column_controls_sidebar)
            load_button_frame.pack(fill=tk.X, pady=5, padx=5)
            tk.Button(load_button_frame, text="Load New Signature Image", command=self.load_signature_image_prompt).pack(fill=tk.X)

            # --- Section 2: Available Signatures (Loaded but not yet placed) ---
            tk.Label(self.column_controls_sidebar, text="Available for Placing:", anchor="w").pack(fill=tk.X, pady=(10,2), padx=5)
            available_list_container = tk.Frame(self.column_controls_sidebar, bd=1, relief=tk.SUNKEN)
            available_list_container.pack(fill=tk.X, padx=5, pady=(0,10))
            
            if not self.loaded_signature_pil_images:
                tk.Label(available_list_container, text="(None loaded)").pack(pady=5)
            else:
                for idx, (_, _, display_name) in enumerate(self.loaded_signature_pil_images):
                    f_avail = tk.Frame(available_list_container)
                    f_avail.pack(fill=tk.X, padx=2, pady=1)
                    bg_color = "lightyellow" if idx == self.active_signature_pil_idx_to_place.get() else f_avail.cget("bg")
                    
                    avail_label_text = f"{idx+1}. {display_name[:20]}{'...' if len(display_name) > 20 else ''}"
                    avail_label = tk.Label(f_avail, text=avail_label_text, anchor="w", bg=bg_color, padx=3)
                    avail_label.pack(side=tk.LEFT, fill=tk.X, expand=True)
                    avail_label.bind("<Button-1>", lambda e, i=idx: self._set_active_signature_for_placing(i))

            # --- Section 2.5: Delete Selected Signature Button (if a signature is selected) ---
            if self.selected_placed_signature_idx.get() != -1:
                delete_button_frame = tk.Frame(self.column_controls_sidebar)
                delete_button_frame.pack(fill=tk.X, pady=(10,0), padx=5)
                tk.Button(delete_button_frame, text="Delete Selected", command=self.delete_selected_placed_signature, bg="salmon").pack(fill=tk.X)
            
            # --- Section 3: Placed Signatures on Document ---
            tk.Label(self.column_controls_sidebar, text="Placed on Document:", anchor="w").pack(fill=tk.X, pady=(10,2), padx=5)
            selected_placed_idx = self.selected_placed_signature_idx.get()
            for idx, sig_data_item in enumerate(self.placed_signatures_data):
                pil_image_idx = sig_data_item['pil_image_idx']
                _, _, display_name = self.loaded_signature_pil_images[pil_image_idx]
                
                item_frame = tk.Frame(self.column_controls_sidebar, bd=1, relief=tk.SOLID)
                item_frame.pack(fill=tk.X, padx=5, pady=3)
                if idx == selected_placed_idx:
                    item_frame.config(bg="lightblue") # Highlight selected

                label_text = f"Sig {idx + 1}: {display_name[:15]}{'...' if len(display_name) > 15 else ''}" # Truncate name
                tk.Label(item_frame, text=label_text, anchor="w").pack(side=tk.LEFT, padx=(2,5), fill=tk.X, expand=True)
                
                tk.Button(item_frame, text="Del", command=lambda i=idx: self._handle_sidebar_delete_signature(i), width=3).pack(side=tk.RIGHT, padx=(0,2))
                tk.Button(item_frame, text="Sel", command=lambda i=idx: self._handle_sidebar_select_signature(i), width=3).pack(side=tk.RIGHT, padx=(0,2))
            
            if not self.placed_signatures_data:
                 tk.Label(self.column_controls_sidebar, text="(None placed on document)", justify=tk.CENTER).pack(pady=10)


        else: # Text injection mode
            if self.num_excel_cols == 0:
                tk.Label(self.column_controls_sidebar, text="Load Excel file\nto define text fields.", justify=tk.CENTER).pack(pady=20)
                return

            for i in range(self.num_excel_cols):
                rtl_var = tk.BooleanVar(value=True) # Default to True for Hebrew context
                rtl_var.trace_add("write", self._on_font_change) # Update preview on change
                self.is_rtl_vars.append(rtl_var)

                status_var = tk.StringVar(value="✖") # Default to not placed
                if i < len(self.coords_pdf) and self.coords_pdf[i] is not None:
                    status_var.set("✔") # Set to placed if coord exists
                self.col_status_vars.append(status_var)

                item_frame = tk.Frame(self.column_controls_sidebar, bd=1, relief=tk.SOLID)
                item_frame.pack(fill=tk.X, padx=5, pady=3)

                status_label_text = f"Col {i+1}:"
                
                tk.Label(item_frame, textvariable=status_var, width=2, font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=(2,0))
                tk.Label(item_frame, text=status_label_text).pack(side=tk.LEFT, padx=(0,5))
                
                ttk.Checkbutton(item_frame, text="RTL", variable=rtl_var, width=5).pack(side=tk.LEFT, padx=(0,5))
                tk.Button(item_frame, text="Move", command=lambda idx=i: self.prepare_to_set_coord(idx)).pack(side=tk.LEFT, padx=5)

    def _handle_sidebar_select_signature(self, sig_idx):
        self._select_placed_signature(sig_idx)

    def _handle_sidebar_delete_signature(self, sig_idx):
        self.selected_placed_signature_idx.set(sig_idx) # Set as selected for deletion logic
        self.delete_selected_placed_signature()

    def _set_active_signature_for_placing(self, pil_idx):
        if 0 <= pil_idx < len(self.loaded_signature_pil_images):
            self.active_signature_pil_idx_to_place.set(pil_idx)
            self.status_label.config(text=f"Ready to place: {self.loaded_signature_pil_images[pil_idx][2]}. Click on PDF.")
            self._build_dynamic_coord_controls() # Refresh sidebar to show selection

    def _on_font_change(self, *args):
        if self.is_text_preview_active and not self.signature_mode_active.get():
            self._update_text_preview()

    def prepare_to_set_coord(self, col_idx):
        if self.pdf_doc:
            self.active_coord_to_set_idx = col_idx
            self.status_label.config(text=f"Select position for column {col_idx + 1} on the image, or drag the marker.")
            self._drag_data["item"] = None
            # If text preview is active, update it to potentially clear old highlights or focus
            if self.is_text_preview_active:
                self._update_text_preview()
        else:
            self.status_label.config(text="Please load a PDF file first.")

    def _change_preview_row(self, direction):
        if self.excel_data_preview is None or self.excel_data_preview.empty:
            return

        current_idx = self.preview_row_index.get()
        new_idx = current_idx + direction
        num_rows = self.excel_data_preview.shape[0]

        if 0 <= new_idx < num_rows:
            self.preview_row_index.set(new_idx)
            self._update_preview_row_display_and_buttons()
            if self.is_text_preview_active:
                self._update_text_preview()

    def _update_preview_row_display_and_buttons(self):
        if self.excel_data_preview is not None and not self.excel_data_preview.empty:
            current_idx = self.preview_row_index.get()
            num_rows = self.excel_data_preview.shape[0]
            self.preview_row_display.set(f"Row: {current_idx + 1}")

            self.prev_row_button.config(state=tk.NORMAL if current_idx > 0 else tk.DISABLED)
            self.next_row_button.config(state=tk.NORMAL if current_idx < num_rows - 1 else tk.DISABLED)
        else:
            self.preview_row_display.set("Row: -")
            self.prev_row_button.config(state=tk.DISABLED)
            self.next_row_button.config(state=tk.DISABLED)

    def _handle_mouse_wheel_zoom(self, event):
        if not self.pdf_doc:
            return

        # Get mouse position on canvas (relative to the top-left of the scrollable content)
        # and widget coordinates (relative to the canvas widget itself)
        mouse_x_on_image_before_zoom = self.canvas.canvasx(event.x)
        mouse_y_on_image_before_zoom = self.canvas.canvasy(event.y)

        factor_change = 0
        # Respond to Linux wheel events
        if event.num == 4: # Scroll up
            factor_change = 0.1
        elif event.num == 5: # Scroll down
            factor_change = -0.1
        # Respond to Windows/Mac wheel events
        elif event.delta > 0: # Scroll up
            factor_change = 0.1
        elif event.delta < 0: # Scroll down
            factor_change = -0.1
        
        if factor_change != 0:
            # Pass mouse coordinates to the zoom function
            self.zoom(factor_change, mouse_x_on_image_before_zoom, mouse_y_on_image_before_zoom, event.x, event.y)

    def zoom(self, factor_change, mouse_x_img_old=None, mouse_y_img_old=None, mouse_widget_x=None, mouse_widget_y=None):
        """
        Zooms the PDF preview.
        If mouse coordinates are provided, zooms towards the mouse cursor.
        Otherwise (e.g., for button clicks), attempts to maintain the current view.
        """
        if not self.pdf_doc:
            return

        old_zoom = self.current_zoom_factor.get()
        potential_new_zoom = old_zoom + factor_change

        # Clamp new_zoom to min/max values
        if potential_new_zoom < 0.2:
            new_zoom = 0.2
        elif potential_new_zoom > 5.0:
            new_zoom = 5.0
        else:
            new_zoom = round(potential_new_zoom, 2)

        if new_zoom == old_zoom:  # No actual change in zoom level
            return

        # Store old scroll fractions if this is a button zoom (no mouse coords)
        old_view_x_fraction = 0.0
        old_view_y_fraction = 0.0
        if mouse_x_img_old is None: # Indicates a button press or other non-mouse-centric zoom
            old_view_x_fraction = self.canvas.xview()[0]
            old_view_y_fraction = self.canvas.yview()[0]

        self.current_zoom_factor.set(new_zoom)
        self.zoom_display_var.set(f"Zoom: {int(new_zoom * 100)}%")
        
        self._redisplay_pdf_page() # This updates self.image_on_canvas_width_px etc. based on new_zoom

        if mouse_x_img_old is not None and mouse_y_img_old is not None and \
           mouse_widget_x is not None and mouse_widget_y is not None and old_zoom > 0:
            
            # Point on the original unzoomed PDF (or its 100% zoom canvas equivalent) that was under the mouse.
            original_point_x = mouse_x_img_old / old_zoom
            original_point_y = mouse_y_img_old / old_zoom

            # New coordinates of this point on the *newly-zoomed* image
            new_target_image_x = original_point_x * new_zoom
            new_target_image_y = original_point_y * new_zoom

            # We want this new_target_image_x/y to be under the mouse cursor's widget position (mouse_widget_x, mouse_widget_y).
            # So, the new top-left of the view (scroll position) should be:
            new_scroll_x = new_target_image_x - mouse_widget_x
            new_scroll_y = new_target_image_y - mouse_widget_y
            
            fraction_x = new_scroll_x / self.image_on_canvas_width_px if self.image_on_canvas_width_px > 0 else 0
            fraction_y = new_scroll_y / self.image_on_canvas_height_px if self.image_on_canvas_height_px > 0 else 0

            self.canvas.xview_moveto(max(0.0, min(1.0, fraction_x))) # Clamp fraction
            self.canvas.yview_moveto(max(0.0, min(1.0, fraction_y))) # Clamp fraction
        elif mouse_x_img_old is None: # Fallback for button zoom: try to restore old view fraction
            self.canvas.xview_moveto(old_view_x_fraction)
            self.canvas.yview_moveto(old_view_y_fraction)

    def _redisplay_pdf_page(self, page_number=None):
        if not self.pdf_doc:
            return

        if page_number is None:
            page_number = self.current_pdf_page_num.get()
        
        # Ensure page_number is valid
        if not (0 <= page_number < self.pdf_doc.page_count):
            # This case should ideally be prevented by disabling nav buttons,
            # but as a safeguard (keeping this print as it indicates a logic flaw if reached):
            print(f"DEBUG: Invalid page number {page_number} requested for redisplay.")
            if self.pdf_doc.page_count > 0:
                page_number = 0 # Default to first page if out of bounds
                self.current_pdf_page_num.set(0)
            else: # No pages in PDF
                self.canvas.delete("all")
                self.photo_image = None
                self.image_on_canvas_width_px = 0
                self.image_on_canvas_height_px = 0
                self.canvas.config(scrollregion=(0,0,0,0))
                return

        page = self.pdf_doc.load_page(page_number)
        zoom_val = self.current_zoom_factor.get()
        mat = fitz.Matrix(zoom_val, zoom_val)
        pix = page.get_pixmap(matrix=mat)

        # Update page dimensions based on the *current* page being displayed (if they can vary)
        self.image_on_canvas_width_px = pix.width
        self.image_on_canvas_height_px = pix.height

        self.photo_image = tk.PhotoImage(data=pix.tobytes("ppm"))

        self.canvas.delete("pdf_image") # Delete only the old PDF image
        self.canvas.create_image(0, 0, anchor=tk.NW, image=self.photo_image, tags="pdf_image")
        self.canvas.config(scrollregion=(0, 0, self.image_on_canvas_width_px, self.image_on_canvas_height_px))

        self._update_page_nav_controls() # Update page display like "Page 1/X"
        self._draw_markers()
        if self.is_text_preview_active:
            if not self.signature_mode_active.get():
                self._update_text_preview()
        if self.signature_mode_active.get():
            self._draw_placed_signatures()

    def _draw_markers(self):
        self.canvas.delete("marker") # Delete all items with the general "marker" tag
        if self.signature_mode_active.get(): return # No text markers in signature mode
        marker_radius = 5
        for i, pdf_coord in enumerate(self.coords_pdf):
            if pdf_coord:
                canvas_coords = self._pdf_coords_to_canvas_coords(pdf_coord)
                if canvas_coords:
                    color = MARKER_COLORS[i % len(MARKER_COLORS)]
                    marker_tag = f"marker_{i}" # Unique tag for each marker based on index
                    self.canvas.create_rectangle(canvas_coords[0] - marker_radius, canvas_coords[1] - marker_radius,
                                                 canvas_coords[0] + marker_radius, canvas_coords[1] + marker_radius,
                                                 fill=color, outline=color, tags=(marker_tag, "marker")) # Add general "marker" tag too

    def _draw_placed_signatures(self):
        self.canvas.delete("signature_instance") # Delete all signature instances
        if not self.signature_mode_active.get() or not self.pdf_doc:
            return

        for idx, sig_data in enumerate(self.placed_signatures_data):
            canvas_params = self._pdf_rect_to_canvas_rect_params(sig_data['pdf_rect_pts'])
            if canvas_params:
                canvas_x, canvas_y, canvas_w, canvas_h = canvas_params
                
                # Ensure width and height are positive for PIL resize
                if canvas_w <= 0 or canvas_h <= 0: continue

                pil_img_original = self.loaded_signature_pil_images[sig_data['pil_image_idx']][0]
                # Resize PIL image for current canvas zoom/size
                # Use ANTIALIAS for better quality if Pillow version supports it, otherwise RESAMPLE.LANCZOS
                try:
                    resample_filter = Image.Resampling.LANCZOS if hasattr(Image, "Resampling") else Image.ANTIALIAS
                    pil_img_resized = pil_img_original.resize((int(canvas_w), int(canvas_h)), resample_filter)
                    # # DEBUG for resize
                    # if self.selected_placed_signature_idx.get() == idx and self._resize_data.get("sig_idx") == idx : # A bit redundant with active check
                    #     print(f"DEBUG DRAW SIG (RESIZING): idx={idx}, pdf_rect_pts={sig_data['pdf_rect_pts']}")
                    #     print(f"  Canvas params for resize: x={canvas_x:.2f}, y={canvas_y:.2f}, w={canvas_w:.2f}, h={canvas_h:.2f}")
                except Exception as e:
                    print(f"Error resizing signature image for canvas: {e}")
                    continue
                
                sig_data['tk_photo'] = ImageTk.PhotoImage(pil_img_resized) # Keep reference
                sig_data['canvas_item_id'] = self.canvas.create_image(canvas_x, canvas_y, anchor=tk.NW, image=sig_data['tk_photo'], tags=("signature_instance", f"sig_{idx}"))
        # Selection highlights are now handled exclusively by _redraw_selection_highlights()
        self._redraw_selection_highlights() # Ensure highlights are correct after redrawing all signatures
    def _pdf_coords_to_canvas_coords(self, pdf_coords_tuple):
        if not self.pdf_doc or self.pdf_page_width_pt == 0 or self.pdf_page_height_pt == 0:
            return None
        pdf_x_pt, pdf_y_pt_from_bottom = pdf_coords_tuple

        # Convert PDF coordinates (origin bottom-left) to canvas image coordinates (origin top-left)
        canvas_x_on_image = (pdf_x_pt / self.pdf_page_width_pt) * self.image_on_canvas_width_px
        
        # PDF Y is from bottom, Canvas Y is from top.
        # So, (1 - (pdf_y / pdf_height)) gives the proportional distance from the top of the PDF.
        canvas_y_on_image = (1 - (pdf_y_pt_from_bottom / self.pdf_page_height_pt)) * self.image_on_canvas_height_px

        return (canvas_x_on_image, canvas_y_on_image)

    def load_pdf_template(self):
        path = filedialog.askopenfilename(
            title="Select PDF File",
            filetypes=(("PDF files", "*.pdf"), ("All files", "*.*"))
        )
        if not path:
            return

        self.pdf_path.set(path)
        self.pdf_display_var.set(os.path.basename(path) if path else "(No file selected)")
        try:
            self.pdf_doc = fitz.open(path)
            if not self.pdf_doc.page_count > 0:
                messagebox.showerror("Error", "The PDF file is empty.")
                self.pdf_doc = None
                return

            page = self.pdf_doc.load_page(0) # Load first page
            self.pdf_page_width_pt = page.rect.width
            self.pdf_page_height_pt = page.rect.height

            self.pdf_total_pages.set(self.pdf_doc.page_count)
            self.current_pdf_page_num.set(0) # Start at the first page
            self.pdf_nav_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(0,2), before=self.status_label) # Show nav controls

            if self.pdf_doc.page_count > 1:
                self.signature_mode_active.set(True)
            else:
                self.signature_mode_active.set(False) # Ensure it's reset if a single page PDF is loaded later
            
            self._on_signature_mode_change() # Update UI based on mode

            self.current_zoom_factor.set(1.0) # Reset zoom
            self.zoom_display_var.set(f"Zoom: 100%")
            # Calculate initial zoom to fit page (optional, or start at 100%)
            # For simplicity, we start at 100% and user can zoom.
            # If you want fit-to-page initially:
            # self.master.update_idletasks()
            # canvas_width_initial = self.canvas.winfo_width()
            # canvas_height_initial = self.canvas.winfo_height()
            # zoom_x_initial = canvas_width_initial / self.pdf_page_width_pt
            # zoom_y_initial = canvas_height_initial / self.pdf_page_height_pt
            # self.current_zoom_factor.set(min(zoom_x_initial, zoom_y_initial, 1.0)) # Fit or 100%

            self._redisplay_pdf_page(page_number=0) # Display first page
            
            if not self.signature_mode_active.get():
                if self.num_excel_cols > 0:
                    self.status_label.config(text=f"PDF file loaded. Click 'Move' next to a column to position it, or click on the image for chronological placement.")
                    if self.is_text_preview_active and any(c is not None for c in self.coords_pdf): # Check if any coord is set
                        self._update_text_preview()
                else:
                    self.status_label.config(text="PDF file loaded. Load an Excel file to define text fields.")
            # else: status already set by _on_signature_mode_change
            
            # No specific column is being set by "Move" button initially
            # self.active_coord_to_set_idx = None # This is already the default
            if not self.signature_mode_active.get():
                self._update_text_preview() # Will clear if coords are None
            
        except Exception as e:
            messagebox.showerror("Error Loading PDF", str(e))
            self.pdf_doc = None
            self.pdf_display_var.set("(Error loading)")
            self.pdf_path.set("")
            self._hide_and_reset_page_nav()


    def load_excel_data(self):
        if self.signature_mode_active.get():
            messagebox.showinfo("Info", "Excel loading is disabled in Signature Mode.")
            return
        path = filedialog.askopenfilename(
            title="Select Excel File",
            filetypes=(("Excel files", "*.xlsx *.xls"), ("All files", "*.*"))
        )
        if not path:
            return
        self.excel_path.set(path)
        self.excel_display_var.set(os.path.basename(path) if path else "(No file selected)")
        try:
            df = pd.read_excel(path, header=None) # Assume no header for simplicity, take first two columns
            if df.empty or df.shape[1] == 0:
                messagebox.showerror("Error", "The Excel file is empty or contains no columns.")
                self.excel_path.set("")
                self.num_excel_cols = 0
                self.excel_display_var.set("(Empty or invalid file)")
                self.coords_pdf = []
                return
            
            self.num_excel_cols = df.shape[1]
            self.coords_pdf = [None] * self.num_excel_cols # Initialize/reset coords list
            # Initialize status vars when Excel is loaded
            self.col_status_vars = [tk.StringVar(value="✖") for _ in range(self.num_excel_cols)]
            self._build_dynamic_coord_controls() # Rebuild UI for coordinates
            
            # Improved Excel Preview
            preview_text_summary = "Excel Preview Summary:\n" # For internal data, not displayed directly
            if not df.empty:
                # Preview first row
                if df.shape[1] >= 1: # Check if there's at least one column
                    val1_r1 = str(df.iloc[0, 0]) if pd.notna(df.iloc[0, 0]) else ""
                    preview_text_summary += f"Row 1: Col 1 = {val1_r1}"
                    if self.num_excel_cols >= 2: # Check if there's a second column
                        val2_r1 = str(df.iloc[0, 1]) if pd.notna(df.iloc[0,1]) else ""
                        preview_text_summary += f", Col 2 = {val2_r1 if self.num_excel_cols > 1 else ''}"
                else:
                    preview_text_summary += "Row 1: (No data columns)"

                # Preview second row if it exists
                if df.shape[0] > 1: # Check if there's a second row
                    preview_text_summary += "\n"
                    if df.shape[1] >= 1:
                        val1_r2 = str(df.iloc[1, 0]) if pd.notna(df.iloc[1, 0]) else ""
                        preview_text_summary += f"Row 2: Col 1 = {val1_r2}"
                        if self.num_excel_cols >= 2:
                            val2_r2 = str(df.iloc[1, 1]) if pd.notna(df.iloc[1,1]) else ""
                            preview_text_summary += f", Col 2 = {val2_r2 if self.num_excel_cols > 1 else ''}"
            else:
                preview_text_summary += "Excel file is empty."
            self.excel_preview_text.set(preview_text_summary) # Store summary, not directly displayed as a label anymore
            if self.pdf_doc:
                 self.status_label.config(text=f"Excel loaded ({self.num_excel_cols} cols). Click on image to position Col 1, or use 'Move'.")
            else:
                 self.status_label.config(text=f"Excel loaded ({self.num_excel_cols} cols). Load PDF to start positioning.")
            self.excel_data_preview = df
            self.preview_row_index.set(0) # Reset to first row for preview
            self._update_preview_row_display_and_buttons() # Update buttons AFTER df is set
            # Try to update preview if PDF is also loaded and at least one coord is set
            if self.is_text_preview_active and self.pdf_doc and any(c is not None for c in self.coords_pdf):
                self._update_text_preview()
        except Exception as e:
            messagebox.showerror("Error Loading Excel", str(e))
            self.excel_path.set("")
            self.excel_display_var.set("(Error loading)")
            self.excel_preview_text.set("Excel Preview: (Error loading)")
            self.num_excel_cols = 0
            self.preview_row_index.set(0)
            self._update_preview_row_display_and_buttons()
            self._build_dynamic_coord_controls()
            self.excel_data_preview = None

    def select_output_dir(self):
        path = filedialog.askdirectory(title="Select Output Folder")
        if not path:
            return
        self.output_dir.set(path)
        self.output_dir_display_var.set(os.path.basename(path) if path else "(No folder selected)")
        self.status_label.config(text=f"Output folder selected: {path}")

    def _hide_and_reset_page_nav(self):
        self.pdf_nav_frame.pack_forget()
        self.current_pdf_page_num.set(0)
        self.pdf_total_pages.set(0)
        self.pdf_page_display_var.set("Page: -/-")

    def _update_page_nav_controls(self):
        if not self.pdf_doc or self.pdf_total_pages.get() == 0:
            self._hide_and_reset_page_nav()
            return

        current_page_0_indexed = self.current_pdf_page_num.get()
        total_pages = self.pdf_total_pages.get()
        self.pdf_page_display_var.set(f"Page {current_page_0_indexed + 1}/{total_pages}")

        self.prev_pdf_page_button.config(state=tk.NORMAL if current_page_0_indexed > 0 else tk.DISABLED)
        self.next_pdf_page_button.config(state=tk.NORMAL if current_page_0_indexed < total_pages - 1 else tk.DISABLED)

    def _change_pdf_page(self, delta):
        new_page_num = self.current_pdf_page_num.get() + delta
        if 0 <= new_page_num < self.pdf_total_pages.get():
            self.current_pdf_page_num.set(new_page_num)
            self._redisplay_pdf_page(page_number=new_page_num) # This will also call _update_page_nav_controls
    def _canvas_coords_to_pdf_coords(self, canvas_x, canvas_y):
        """Converts canvas click coordinates to PDF points (bottom-left origin)."""
        if not self.pdf_doc or self.image_on_canvas_width_px == 0 or self.image_on_canvas_height_px == 0:
            return None

        prop_x = canvas_x / self.image_on_canvas_width_px
        prop_y = canvas_y / self.image_on_canvas_height_px

        pdf_x_pt = prop_x * self.pdf_page_width_pt # Use original PDF width for calculation
        pdf_y_pt_from_top = prop_y * self.pdf_page_height_pt # Use original PDF height
        pdf_y_pt_from_bottom = self.pdf_page_height_pt - pdf_y_pt_from_top

        return (pdf_x_pt, pdf_y_pt_from_bottom)

    def _on_canvas_b1_press(self, event):
        # Check if the click is on an existing marker.
        # The marker's own tag binding (on_marker_press) will handle the drag initiation.
        current_item_tuple = self.canvas.find_withtag(tk.CURRENT)
        if current_item_tuple:
            # If it's a signature, let its specific handler take over
            item_id = current_item_tuple[0]
            tags = self.canvas.gettags(item_id)
            if "signature_instance" in tags:
                # on_placed_signature_press will be called by its tag_bind.
                # Return "break" to prevent canvas's default B1 press (like scan_mark).
                return "break" 
            if "marker" in tags:
                # Let on_marker_press (already bound to the marker tag) handle this.
                # on_marker_press will set self._drag_data["item"].
                # Return "break" to prevent canvas's default B1 press.
                return "break"

        # If not on a draggable item, this B1 press is for the canvas itself (pan or click-to-place).
        if not self.pdf_doc:
            self.status_label.config(text="Please load a PDF file first.")
            return

        # Store press coordinates and prepare for potential pan
        self._pan_data["press_x"] = self.canvas.canvasx(event.x) # Use canvas coords
        self._pan_data["press_y"] = self.canvas.canvasy(event.y) # Use canvas coords
        self._pan_data["is_potential_pan_or_click"] = True
        self._pan_data["has_dragged_for_pan"] = False
        self.canvas.scan_mark(event.x, event.y) # For scan_dragto, event.x/y is fine

    def _on_canvas_b1_motion(self, event):
        # print(f"DEBUG: _on_canvas_b1_motion entered. _drag_data: {self._drag_data}, _pan_data: {self._pan_data}") # Reduced verbosity
        # Prioritize resize check
        if self._resize_data["active"]:            
            sig_idx = self._resize_data["sig_idx"]
            sig_data = self.placed_signatures_data[sig_idx]
            # Ensure original_pdf_rect is a valid Rect object before proceeding
            if not isinstance(self._resize_data["original_pdf_rect"], fitz.Rect):
                print("CRITICAL: _on_canvas_b1_motion - original_pdf_rect is not a Rect object during resize. Bailing.") # Kept for critical error
                return "break" # Or handle error appropriately
            original_pdf_rect = self._resize_data["original_pdf_rect"]
            aspect_ratio = self._resize_data["aspect_ratio"]
            handle_type = self._resize_data["handle_type"]

            current_mouse_x_canvas = self.canvas.canvasx(event.x)
            current_mouse_y_canvas = self.canvas.canvasy(event.y)

            # Convert current mouse to PDF coordinates (y from top)
            current_mouse_pdf_x, current_mouse_pdf_y = self._canvas_pos_to_pdf_pos_tl(current_mouse_x_canvas, current_mouse_y_canvas)
            if current_mouse_pdf_x is None: return "break" # Clicked outside image

            new_rect = fitz.Rect(original_pdf_rect.x0, original_pdf_rect.y0, original_pdf_rect.x1, original_pdf_rect.y1)
            min_pdf_dim = 10 # Minimum dimension in PDF points
            # Store w,h before aspect ratio for debugging
            debug_w_before_aspect, debug_h_before_aspect = 0,0            

            # Calculate new dimensions based on mouse and fixed corner, then apply aspect ratio
            if handle_type == "br": # Bottom-Right handle; Top-Left is fixed
                w = current_mouse_pdf_x - new_rect.x0
                h = current_mouse_pdf_y - new_rect.y0
                if aspect_ratio > 0:
                    if w / aspect_ratio > h: 
                        h = w / aspect_ratio # Adjust height based on width
                    else: w = h * aspect_ratio # Adjust width based on height
                new_rect.x1 = new_rect.x0 + max(w, min_pdf_dim)
                new_rect.y1 = new_rect.y0 + max(h, min_pdf_dim)

            elif handle_type == "tl": # Top-Left handle; Bottom-Right is fixed
                w = new_rect.x1 - current_mouse_pdf_x
                h = new_rect.y1 - current_mouse_pdf_y
                if aspect_ratio > 0:
                    if w / aspect_ratio > h: h = w / aspect_ratio
                    else: w = h * aspect_ratio
                new_rect.x0 = new_rect.x1 - max(w, min_pdf_dim)
                new_rect.y0 = new_rect.y1 - max(h, min_pdf_dim)

            elif handle_type == "tr": # Top-Right handle; Bottom-Left is fixed
                w = current_mouse_pdf_x - new_rect.x0
                h = new_rect.y1 - current_mouse_pdf_y
                if aspect_ratio > 0:
                    if w / aspect_ratio > h: h = w / aspect_ratio
                    else: w = h * aspect_ratio
                new_rect.x1 = new_rect.x0 + max(w, min_pdf_dim)
                new_rect.y0 = new_rect.y1 - max(h, min_pdf_dim)

            elif handle_type == "bl": # Bottom-Left handle; Top-Right is fixed
                w = new_rect.x1 - current_mouse_pdf_x
                h = current_mouse_pdf_y - new_rect.y0
                if aspect_ratio > 0:
                    if w / aspect_ratio > h: h = w / aspect_ratio
                    else: w = h * aspect_ratio
                new_rect.x0 = new_rect.x1 - max(w, min_pdf_dim)
                new_rect.y1 = new_rect.y0 + max(h, min_pdf_dim)
            # # DEBUG RESIZE MOTION: sig_idx={sig_idx}, handle={handle_type}
            # # print(f"  Original PDF Rect: {original_pdf_rect}")
            # # print(f"  Mouse PDF (TL): {current_mouse_pdf_x:.2f}, {current_mouse_pdf_y:.2f}")
            # # print(f"  Calc w={w:.2f}, h={h:.2f} (after aspect, before max with min_pdf_dim)") # This w,h is for the specific handle logic
            # # print(f"  New PDF Rect: x0={new_rect.x0:.2f}, y0={new_rect.y0:.2f}, x1={new_rect.x1:.2f}, y1={new_rect.y1:.2f}, W={new_rect.width:.2f}, H={new_rect.height:.2f}")
            
            sig_data['pdf_rect_pts'] = new_rect
            self._draw_placed_signatures() # Redraws signature and its selection/handles
            # Update status bar or any display of size if needed
            # self.status_label.config(text=f"Resizing: W:{new_rect.width:.1f}, H:{new_rect.height:.1f} pt")
            return "break" # Consume event

        # Then check for other item drags (like signature move or marker move)
        elif self._item_drag_active: 
            # An item (marker or signature image) is being dragged.
            # Its specific <B1-Motion> tag binding (e.g., on_placed_signature_motion, on_marker_motion)
            # should handle this. This general canvas motion handler should let the event propagate
            # to those more specific handlers if they exist and are designed to take over.
            # If those handlers consume the event (return "break"), this part won't matter.
            pass 
        
        # If no resize and no other item drag, then it's for canvas panning.
        else:
            # No item drag is active, so this motion is for canvas panning.
            # # print("DEBUG: _on_canvas_b1_motion: _item_drag_active is False. Proceeding with pan logic.") # Reduced verbosity
            if self._pan_data["is_potential_pan_or_click"]:
                # This block is for canvas panning if no item drag is active.
                if not self._pan_data["has_dragged_for_pan"]: # Check only once if it becomes a drag
                    # Check if movement exceeds threshold for panning
                    # Use canvas coordinates for calculating drag distance
                    current_canvas_x = self.canvas.canvasx(event.x)
                    current_canvas_y = self.canvas.canvasy(event.y)
                    dx = abs(current_canvas_x - self._pan_data["press_x"])
                    dy = abs(current_canvas_y - self._pan_data["press_y"])

                    if dx > self._pan_data["pan_threshold"] or dy > self._pan_data["pan_threshold"]:
                        self._pan_data["has_dragged_for_pan"] = True
                
                if self._pan_data["has_dragged_for_pan"]:
                    if self.pdf_doc: # Ensure PDF is loaded before trying to pan
                        self.canvas.config(cursor="fleur")
                        self.canvas.scan_dragto(event.x, event.y, gain=1) # event.x/y is fine for scan_dragto

    def _on_canvas_b1_release(self, event):
        # If a marker drag was just completed, self._drag_data["item"] would have been cleared by on_marker_release.
        # We primarily care about actions initiated by _on_canvas_b1_press here.
        # # print(f"DEBUG CANVAS B1 RELEASE: _resize_data[active]={self._resize_data['active']}, _item_drag_active={self._item_drag_active}, _drag_data={self._drag_data}, _pan_data[is_potential]={self._pan_data['is_potential_pan_or_click']}")

        if self._resize_data["active"]:
            sig_idx = self._resize_data["sig_idx"] # This was part of the if block
            self._resize_data["active"] = False 
            self._item_drag_active = False 
            self.canvas.config(cursor="")
            # Final update of size in status or data model if needed
            if 0 <= sig_idx < len(self.placed_signatures_data):
                 self.status_label.config(text=f"Signature {sig_idx+1} resized.")
            
            self._build_dynamic_coord_controls() 
            self._redraw_selection_highlights() # Ensure handles are correctly redrawn after resize
            return "break" # Consume event
        if self._pan_data["is_potential_pan_or_click"]:
            if self._pan_data["has_dragged_for_pan"]:
                # Pan occurred
                self.canvas.config(cursor="") # Reset cursor from "fleur"
            else:
                # No significant drag, so it's a click-to-place action.
                # Ensure that a marker drag didn't *just* happen and clear _drag_data["item"]
                # If _drag_data["item"] is None now, it means either no marker drag started,
                # or a marker drag finished. We only want to place if no marker drag was involved.
                # The check in _on_canvas_b1_press (find_withtag) should prevent this path if a marker was initially clicked.
                if not self._drag_data.get("item"): # Use .get() for safer access
                # if not self._item_drag_active: # Check our flag
                    # If we are in signature mode, and _drag_data["item"] is None,
                    # it means the click was not on an existing signature (which would have set _drag_data["item"])
                    # and not on a marker. So, it's a click on empty space.                    
                    if self.signature_mode_active.get():
                        self._execute_place_signature_at_click(event)
                    elif not self.signature_mode_active.get(): # Ensure not in sig mode for marker placement
                        self._execute_place_marker_at_click(event)
                # else: if _drag_data["item"] is set, it means an interaction with an existing
                # marker or signature just occurred (e.g., selection click), and we shouldn't place a new one.
                # The respective release handlers (on_marker_release, on_placed_signature_release)
                # will clear _drag_data.                        

            # Reset pan_data for the next B1 interaction on the canvas
            self._pan_data["is_potential_pan_or_click"] = False
            self._pan_data["has_dragged_for_pan"] = False
            # self._item_drag_active = False # Reset here if not reset in item's release

            # Do NOT clear _drag_data here if it was set by on_placed_signature_press for selection,
            # as on_placed_signature_release will handle it.            
            
    def _execute_place_marker_at_click(self, event):
        if not self.pdf_doc: # This check is good to have here too
            return

        idx_to_update = -1

        if self.active_coord_to_set_idx is not None: # User clicked "Move" button for a specific column
            idx_to_update = self.active_coord_to_set_idx
        else: # No specific column chosen, try to find the next unassigned one
            if self.num_excel_cols > 0 and self.coords_pdf:
                try:
                    idx_to_update = self.coords_pdf.index(None) # Find first unassigned coordinate
                except ValueError: # All coordinates are assigned
                    self.status_label.config(text="All columns positioned. Use 'Move' button or drag markers to change.")
                    return
            else: # No Excel loaded or no columns
                self.status_label.config(text="Load Excel file to define columns for positioning.")
                return

        if idx_to_update != -1:
            # Convert event coordinates to canvas coordinates (accounts for scrolling)
            canvas_x = self.canvas.canvasx(event.x)
            canvas_y = self.canvas.canvasy(event.y)

            if not (0 <= canvas_x <= self.image_on_canvas_width_px and \
                    0 <= canvas_y <= self.image_on_canvas_height_px):
                self.status_label.config(text="Click within the image boundaries.")
                return

            pdf_coords = self._canvas_coords_to_pdf_coords(canvas_x, canvas_y)
            if not pdf_coords:
                self.status_label.config(text="Error calculating coordinates.")
                return

            self.coords_pdf[idx_to_update] = pdf_coords
            if idx_to_update < len(self.col_status_vars):
                self.col_status_vars[idx_to_update].set("✔")
            
            # Check if there's a next unassigned coordinate
            next_unassigned_idx = -1
            try:
                next_unassigned_idx = self.coords_pdf.index(None)
            except ValueError: # All assigned
                pass # next_unassigned_idx remains -1
            status_msg = f"Column {idx_to_update + 1} positioned. "
            self.status_label.config(text=status_msg + (f"Click to position column {next_unassigned_idx + 1}." if next_unassigned_idx != -1 else "All columns positioned."))
            self.active_coord_to_set_idx = None # Reset specific "Move" selection after any click
            
            self._draw_markers() 
            if self.is_text_preview_active: # Update preview if active
                self._update_text_preview()

    def _execute_place_signature_at_click(self, event):
        if not self.pdf_doc or not self.signature_mode_active.get():
            return
        # # print(f"DEBUG: _execute_place_signature_at_click: active_signature_pil_idx_to_place is {self.active_signature_pil_idx_to_place.get()}")
        # # print(f"DEBUG: _execute_place_signature_at_click: len(self.loaded_signature_pil_images) is {len(self.loaded_signature_pil_images)}")
        
        active_pil_idx = self.active_signature_pil_idx_to_place.get()
        if active_pil_idx == -1 or active_pil_idx >= len(self.loaded_signature_pil_images):
            self.status_label.config(text="Please select a signature image from the list to place.")
            return

        canvas_x_click = self.canvas.canvasx(event.x)
        canvas_y_click = self.canvas.canvasy(event.y)

        if not (0 <= canvas_x_click <= self.image_on_canvas_width_px and \
                0 <= canvas_y_click <= self.image_on_canvas_height_px):
            self.status_label.config(text="Please click within the image boundaries.")
            return

        pdf_tl_x_pt, pdf_tl_y_pt = self._canvas_pos_to_pdf_pos_tl(canvas_x_click, canvas_y_click)
        
        pil_img, img_path, display_name = self.loaded_signature_pil_images[active_pil_idx]
        aspect_ratio = pil_img.width / pil_img.height if pil_img.height > 0 else 1
        
        # Use default width for initial placement, calculate height
        sig_width_pt = DEFAULT_SIGNATURE_WIDTH_PT 
        sig_height_pt = DEFAULT_SIGNATURE_WIDTH_PT / aspect_ratio if aspect_ratio > 0 else DEFAULT_SIGNATURE_WIDTH_PT


        pdf_rect = fitz.Rect(pdf_tl_x_pt, pdf_tl_y_pt, pdf_tl_x_pt + sig_width_pt, pdf_tl_y_pt + sig_height_pt)

        new_sig_data = {
            'pil_image_idx': active_pil_idx,
            'pdf_rect_pts': pdf_rect,
            'aspect_ratio': aspect_ratio,
            'selected': False # Initially not selected after placement
        }
        # # print(f"DEBUG: _execute_place_signature_at_click: placing signature with pil_image_idx {new_sig_data['pil_image_idx']}")
        self.placed_signatures_data.append(new_sig_data)
        self._draw_placed_signatures() # Redraws all images and then calls _redraw_selection_highlights()
        
        self.active_signature_pil_idx_to_place.set(-1) # Reset after placement
        self._build_dynamic_coord_controls() # Update sidebar
        
        self.status_label.config(text=f"Signature '{display_name}' added. Click to select or drag.")
    
    def on_marker_press(self, event):
        item = self.canvas.find_withtag(tk.CURRENT) # Get item under cursor
        if not item:
            return
        item_id = item[0]
        tags = self.canvas.gettags(item_id)

        col_idx = -1
        for tag in tags:
            if tag.startswith("marker_"):
                try:
                    col_idx = int(tag.split("_")[1])
                    break
                except ValueError:
                    continue
        if col_idx == -1: return # Not a marker we are interested in
        
        self._drag_data["item"] = item_id # This is the canvas item_id of the marker
        self._drag_data["col_idx"] = col_idx
        self._drag_data["x"] = self.canvas.canvasx(event.x)
        self._drag_data["y"] = self.canvas.canvasy(event.y)
        self.active_coord_to_set_idx = None # Cancel click-to-set mode
        self._item_drag_active = True # Signal that an item drag has started

    def on_marker_motion(self, event):
        if not self._drag_data["item"]:
            return # No item being dragged

        current_x = self.canvas.canvasx(event.x)
        current_y = self.canvas.canvasy(event.y)
        
        dx = current_x - self._drag_data["x"]
        dy = current_y - self._drag_data["y"]

        self.canvas.move(self._drag_data["item"], dx, dy)

        self._drag_data["x"] = current_x
        self._drag_data["y"] = current_y

        # Update PDF coordinates
        marker_coords_canvas = self.canvas.coords(self._drag_data["item"]) # x1, y1, x2, y2
        # Center of the oval marker
        new_canvas_center_x = (marker_coords_canvas[0] + marker_coords_canvas[2]) / 2
        new_canvas_center_y = (marker_coords_canvas[1] + marker_coords_canvas[3]) / 2
        
        pdf_coords = self._canvas_coords_to_pdf_coords(new_canvas_center_x, new_canvas_center_y)

        current_col_idx = self._drag_data.get("col_idx")
        if pdf_coords and current_col_idx is not None and 0 <= current_col_idx < len(self.coords_pdf):
            self.coords_pdf[current_col_idx] = pdf_coords
            # self.coord_texts[current_col_idx].set(f"מיקום {current_col_idx+1}: ({pdf_coords[0]:.1f}, {pdf_coords[1]:.1f}) נק'")
            
            if self.is_text_preview_active:
                self._update_text_preview()
        
        return "break" # Consume event to prevent canvas pan while dragging marker

    def on_marker_release(self, event):
        if not self._drag_data["item"]:
            return
        # Final update after drag, ensuring the latest position is used
        # This is mostly redundant if on_marker_motion updates correctly, but good for safety
        marker_coords_canvas = self.canvas.coords(self._drag_data["item"])
        new_canvas_center_x = (marker_coords_canvas[0] + marker_coords_canvas[2]) / 2
        new_canvas_center_y = (marker_coords_canvas[1] + marker_coords_canvas[3]) / 2
        pdf_coords = self._canvas_coords_to_pdf_coords(new_canvas_center_x, new_canvas_center_y)

        current_col_idx = self._drag_data.get("col_idx")
        if pdf_coords and current_col_idx is not None and 0 <= current_col_idx < len(self.coords_pdf):
            self.coords_pdf[current_col_idx] = pdf_coords
            # self.coord_texts[current_col_idx].set(f"מיקום {current_col_idx+1}: ({pdf_coords[0]:.1f}, {pdf_coords[1]:.1f}) נק'")
            if current_col_idx < len(self.col_status_vars):
                 self.col_status_vars[current_col_idx].set("✔")
            self.status_label.config(text=f"Column {current_col_idx + 1} position updated by dragging.")

        self._drag_data["item"] = None
        self._drag_data["col_idx"] = None
        self._item_drag_active = False # Signal that item drag has ended
        
        if self.is_text_preview_active: # Ensure preview updates on drag release
            self._update_text_preview()

    def on_marker_double_click(self, event):
        item = self.canvas.find_withtag(tk.CURRENT) # Get item under cursor
        if not item:
            return
        item_id = item[0]
        tags = self.canvas.gettags(item_id)

        col_idx = -1
        for tag in tags:
            if tag.startswith("marker_"):
                try:
                    col_idx = int(tag.split("_")[1])
                    break
                except ValueError:
                    continue
        
        if col_idx != -1 and 0 <= col_idx < len(self.is_rtl_vars): # Check if col_idx is valid for is_rtl_vars
            current_rtl_var = self.is_rtl_vars[col_idx] # Get the BooleanVar for this column
            current_rtl_var.set(not current_rtl_var.get()) # Toggle the boolean variable
            # The trace on is_rtl_vars will call _on_font_change, which updates the preview.
            self.status_label.config(text=f"Column {col_idx + 1} direction changed to {'RTL' if current_rtl_var.get() else 'LTR'}.")

    def on_placed_signature_press(self, event):
        # current_tags = self.canvas.gettags(tk.CURRENT) # Debug
        # print(f"DEBUG: on_placed_signature_press: event on item with tags {current_tags}") # Debug
        
        item_tuple = self.canvas.find_withtag(tk.CURRENT)
        if not item_tuple: return
        item_id = item_tuple[0]
        # Find which signature index this item_id corresponds to.
        # The item_id here is the one that received the press event.        
        tags = self.canvas.gettags(item_id)

        sig_idx = -1
        for tag in tags:
            if tag.startswith("sig_"):
                try:
                    sig_idx = int(tag.split("_")[1])
                    # Ensure this sig_idx is valid for placed_signatures_data
                    if 0 <= sig_idx < len(self.placed_signatures_data):
                        break
                    # If int() conversion succeeded but index is out of bounds
                    sig_idx = -1 # Reset/confirm sig_idx is -1
                    continue # Move to the next tag
                except ValueError:
                    # If int() conversion failed
                    continue # Move to the next tag
        
        if sig_idx != -1 and 0 <= sig_idx < len(self.placed_signatures_data):
            self._select_placed_signature(sig_idx)
            
            # After _select_placed_signature, the canvas items have been redrawn,
            # The original 'item_id' that was pressed should still be valid.
            # We use 'item_id' (the one that received the event) for dragging.
            self._drag_data["item"] = item_id 
            self._drag_data["sig_idx"] = sig_idx # Index in self.placed_signatures_data
            self._drag_data["x"] = self.canvas.canvasx(event.x) # Store initial canvas coords
            self._drag_data["y"] = self.canvas.canvasy(event.y)
            self._item_drag_active = True # Signal that an item drag has started
            # # print(f"DEBUG: on_placed_signature_press: Dragging item {item_id} (sig_idx {sig_idx}). Stored canvas_item_id in data: {self.placed_signatures_data[sig_idx].get('canvas_item_id')}") # Debug
            # The 'cursor' option is not valid for canvas items via itemconfig.
            # self.canvas.itemconfig(actual_image_item_id_for_drag, cursor="fleur")

            return "break" # Prevent event propagation
        # If sig_idx was not found or invalid, do nothing or handle as an error/missed click


    def on_placed_signature_motion(self, event):
        # # print(f"DEBUG: on_placed_signature_motion: _drag_data: {self._drag_data}") # Reduced verbosity
        
        if not self._drag_data.get("item") or self._drag_data.get("sig_idx") is None:
            return # No item being dragged or sig_idx not set

        sig_idx = self._drag_data["sig_idx"]
        sig_data = self.placed_signatures_data[sig_idx]
        dragged_image_canvas_id = self._drag_data["item"] # The ID of the image being dragged
        
        current_x_canvas = self.canvas.canvasx(event.x)
        current_y_canvas = self.canvas.canvasy(event.y)
        # # print(f"DEBUG: on_placed_signature_motion: sig_idx={sig_idx}, current_x_canvas={current_x_canvas}, current_y_canvas={current_y_canvas}")
        
        dx_canvas = current_x_canvas - self._drag_data["x"]
        dy_canvas = current_y_canvas - self._drag_data["y"]

        # Move the image item on canvas
        self.canvas.move(dragged_image_canvas_id, dx_canvas, dy_canvas)

        # Update the stored PDF coordinates based on the new canvas position of the top-left corner
        new_canvas_x0, new_canvas_y0 = self.canvas.coords(dragged_image_canvas_id) # For create_image, coords returns x,y
        
        pdf_tl_x_pt, pdf_tl_y_pt = self._canvas_pos_to_pdf_pos_tl(new_canvas_x0, new_canvas_y0)
        
        original_width_pt = sig_data['pdf_rect_pts'].width
        original_height_pt = sig_data['pdf_rect_pts'].height

        sig_data['pdf_rect_pts'].x0 = pdf_tl_x_pt
        sig_data['pdf_rect_pts'].y0 = pdf_tl_y_pt
        sig_data['pdf_rect_pts'].x1 = pdf_tl_x_pt + original_width_pt
        sig_data['pdf_rect_pts'].y1 = pdf_tl_y_pt + original_height_pt
        
        self._drag_data["x"] = current_x_canvas
        self._drag_data["y"] = current_y_canvas
        
        # self._draw_placed_signatures() # NO! This was the problem, and is inefficient here.
        # Instead, move the highlight too.
        highlight_tag_on_canvas = f"highlight_for_sig_{sig_idx}"
        resize_handle_tag_on_canvas = f"handle_sig_{sig_idx}"

        current_highlights = self.canvas.find_withtag(highlight_tag_on_canvas)
        if current_highlights:
            # If highlight is a rect based on image, just move it by same delta
            self.canvas.move(current_highlights[0], dx_canvas, dy_canvas)
        
        # Move all resize handles associated with this signature
        current_resize_handles = self.canvas.find_withtag(resize_handle_tag_on_canvas)
        for handle_item_id in current_resize_handles:
            self.canvas.move(handle_item_id, dx_canvas, dy_canvas)

        # Removed: else: self._redraw_selection_highlights()
        # Redrawing all highlights during motion is inefficient and can cause flicker.
        # The handles and highlight are moved directly. A full redraw happens on release.
        return "break" # Prevent event propagation
    def _redraw_selection_highlights(self):
        self.canvas.delete(RESIZE_HANDLE_TAG) # Explicitly delete all old resize handles first
        self.canvas.delete("selection_highlight_tag") # Use a dedicated tag for highlights
        for idx, sig_data in enumerate(self.placed_signatures_data):
            if sig_data.get('selected', False): # No need to check for canvas_item_id, pdf_rect_pts is source
                canvas_params = self._pdf_rect_to_canvas_rect_params(sig_data['pdf_rect_pts'])
                if canvas_params:
                    canvas_x, canvas_y, canvas_w, canvas_h = canvas_params
                    self.canvas.create_rectangle(
                        canvas_x, canvas_y, canvas_x + canvas_w, canvas_y + canvas_h,
                        outline="blue", width=2, dash=(4,2), 
                        tags=("selection_highlight_tag", f"highlight_for_sig_{idx}", "no_drag") # no_drag to prevent interference
                    )
                    # If the image item itself needs to be raised (e.g., if signatures can overlap)
                    if 'canvas_item_id' in sig_data and sig_data['canvas_item_id']:
                        self.canvas.tag_raise(sig_data['canvas_item_id'])
                        # Also raise the highlight so it's on top of the raised item or other items
                        self.canvas.tag_raise(f"highlight_for_sig_{idx}")
                    
                    # Draw resize handles if this signature is selected
                    # Top-left, Top-right, Bottom-right, Bottom-left
                    handles_coords = [
                        (canvas_x, canvas_y, "tl"), (canvas_x + canvas_w, canvas_y, "tr"),
                        (canvas_x + canvas_w, canvas_y + canvas_h, "br"), (canvas_x, canvas_y + canvas_h, "bl")
                    ]
                    for h_x, h_y, h_type in handles_coords:
                        self.canvas.create_rectangle(
                            h_x - RESIZE_HANDLE_OFFSET, h_y - RESIZE_HANDLE_OFFSET,
                            h_x + RESIZE_HANDLE_OFFSET, h_y + RESIZE_HANDLE_OFFSET,
                            fill=RESIZE_HANDLE_COLOR, outline="black", width=1,
                            tags=(RESIZE_HANDLE_TAG, f"handle_sig_{idx}", f"handle_{h_type}")
                        )
                        self.canvas.tag_raise(f"handle_sig_{idx}") # Raise handles above image/highlight

    def on_placed_signature_release(self, event): # Note: Size display update was removed from _redraw_selection_highlights
        if self._drag_data.get("item"):
            # The 'cursor' option is not valid for canvas items via itemconfig.
            # self.canvas.itemconfig(self._drag_data["item"], cursor="")
            pass
        
        # If a resize was active, it should have been handled by _on_canvas_b1_release
        if self._resize_data["active"]:
            return # Already handled

        # Final position update might have happened in motion, but ensure UI reflects it
        sig_idx = self._drag_data.get("sig_idx")
        if sig_idx is not None and 0 <= sig_idx < len(self.placed_signatures_data):
            sig_data = self.placed_signatures_data[sig_idx]
            self.status_label.config(text=f"Signature moved. Width: {sig_data['pdf_rect_pts'].width:.1f}, Height: {sig_data['pdf_rect_pts'].height:.1f} pt")
        
        self._drag_data.clear() # Clear all drag data
        self._item_drag_active = False # Signal that item drag has ended
        # Redraw to remove any temporary drag artifacts if needed, and ensure selection highlight is correct
        self._redraw_selection_highlights() # Ensure highlights are correct after drag

    def _select_placed_signature(self, sig_idx_to_select, from_press_event=False):
        # from_press_event is a hint that this selection might be part of initiating a drag/resize
        for i, sig in enumerate(self.placed_signatures_data):
            sig['selected'] = (i == sig_idx_to_select)
        self.selected_placed_signature_idx.set(sig_idx_to_select)
        # selected_sig_data = self.placed_signatures_data[sig_idx_to_select] # Vars removed

        # # DEBUG: Verify active_signature_pil_idx_to_place after selecting a placed signature
        # This should NOT change active_signature_pil_idx_to_place.
        # print(f"DEBUG: _select_placed_signature: After selecting placed sig {sig_idx_to_select}, active_signature_pil_idx_to_place is {self.active_signature_pil_idx_to_place.get()}")

        if not from_press_event: # Avoid redundant redraw if press event will handle it
            self._redraw_selection_highlights() 
        self._build_dynamic_coord_controls() 

    def toggle_text_preview(self):
        if not self.pdf_doc:
            messagebox.showwarning("Warning", "Please load a PDF file first.")
            return
        if self.excel_data_preview is None or self.excel_data_preview.empty:
            messagebox.showwarning("Warning", "Please load an Excel file with data first.")
            return
        
        if self.signature_mode_active.get():
            messagebox.showinfo("Info", "Text preview is not applicable in Signature Mode.")
            return # Or toggle a different kind of preview if relevant for signatures
        
        # Check if at least one coordinate is set for the existing columns
        if not self.coords_pdf or not any(c is not None for c in self.coords_pdf):
            if self.num_excel_cols > 0:
                messagebox.showwarning("Warning", f"Please select a position for at least one column on the PDF first.")
            else: # Should not happen if Excel is loaded, but as a safeguard
                messagebox.showwarning("Warning", "Please define text fields (load Excel) and select positions.")
            return
        
        # Toggle the state
        new_preview_state = not self.is_text_preview_active
        self.is_text_preview_active = new_preview_state # Set it first
        
        # Then update button text and preview based on the new state
        # (Button text update for Show/Hide can be added here if desired)
        self._update_text_preview()

    def _update_text_preview(self):
        # Clear existing preview text items
        for item_id in self.preview_text_items:
            self.canvas.delete(item_id)
        self.preview_text_items.clear()
        if not self.is_text_preview_active or \
           self.signature_mode_active.get() or \
           not self.pdf_doc or (self.excel_data_preview is None or self.excel_data_preview.empty) or \
           not self.coords_pdf or self.num_excel_cols == 0:
            return

        current_row_idx = self.preview_row_index.get()
        if not (self.excel_data_preview is not None and \
                0 <= current_row_idx < self.excel_data_preview.shape[0]):
            # # print(f"Preview row index {current_row_idx} is out of bounds.") # Debug
            return # Invalid row index for preview
        try:
            font_family = self.font_family_var.get()
            font_size_from_input = self.font_size_var.get()
            if font_size_from_input <= 0: return # Invalid font size

            # Adjust base font size for Tkinter preview if it tends to look larger, then scale with zoom
            current_zoom = self.current_zoom_factor.get()
            adjusted_base_preview_size = font_size_from_input * TKINTER_FONT_SCALE_FACTOR
            preview_font_size = max(1, int(adjusted_base_preview_size * current_zoom))

            try:
                current_tk_font = tkFont.Font(family=font_family, size=preview_font_size)
            except tk.TclError as e: # Fallback if Tkinter can't create the font by name
                print(f"Error loading font '{font_family}' for Tkinter preview: {e}. Falling back to Arial.")
                current_tk_font = tkFont.Font(family="Arial", size=max(1, int(font_size_from_input * current_zoom))) # Fallback uses unscaled base
                # Consider applying TKINTER_FONT_SCALE_FACTOR to fallback as well for consistency:
                # current_tk_font = tkFont.Font(family="Arial", size=preview_font_size)
            for i in range(self.num_excel_cols):
                if i < len(self.coords_pdf) and self.coords_pdf[i] and \
                   i < len(self.is_rtl_vars) and i < self.excel_data_preview.shape[1]:
                    
                    val_preview = str(self.excel_data_preview.iloc[current_row_idx, i]) if pd.notna(self.excel_data_preview.iloc[current_row_idx, i]) else ""
                    # For Tkinter canvas preview, pass the logical string.
                    text_for_preview = val_preview 
                    
                    pdf_coord = self.coords_pdf[i]
                    is_rtl_current = self.is_rtl_vars[i].get()
                else:
                    continue # Skip if data for this column is incomplete

                canvas_coords = self._pdf_coords_to_canvas_coords(pdf_coord)
                if canvas_coords:
                    anchor_val = tk.SE if is_rtl_current else tk.SW
                    if current_tk_font:
                        item_id = self.canvas.create_text(canvas_coords[0], canvas_coords[1], text=text_for_preview,
                                                         font=current_tk_font, anchor=anchor_val, fill="purple", tags="preview_text_item")
                        self.preview_text_items.append(item_id)
                    else:
                        # Should not happen if fallback is in place
                        print("Error: No font object available for preview.")
        except Exception as e:
            print(f"Error updating text preview: {e}") # Log error, don't crash

    def _insert_text_on_pdf_page(self, page, text_value, pdf_coord_tuple, font_family_name, font_file_path, font_size_pt, is_rtl, fitz_font_object):
        """Helper function to insert text onto a PDF page."""
        if pdf_coord_tuple is None:
            return

        bidi_val = get_display(text_value, base_dir='R' if is_rtl else 'L')
        text_width_pt = fitz_font_object.text_length(bidi_val, fontsize=font_size_pt)

        insertion_point_x_pt = pdf_coord_tuple[0]
        # PyMuPDF's insert_text uses y from top of page.
        # self.coords_pdf stores y from bottom of page.
        insertion_point_y_pt = (self.pdf_page_height_pt - pdf_coord_tuple[1]) - Y_OFFSET_PDF_OUTPUT

        if is_rtl:
            insertion_point_x_pt -= text_width_pt

        page.insert_text((insertion_point_x_pt, insertion_point_y_pt),
                           bidi_val,
                           fontname=font_family_name,
                           fontfile=font_file_path,
                           fontsize=font_size_pt,
                           color=DEFAULT_PDF_TEXT_COLOR,
                           rotate=page.rotation)

    def generate_output_pdfs(self):
        if self.signature_mode_active.get():
            messagebox.showerror("Error", "This function is not available in Signature Mode. Use 'Create Signed PDF'.")
            return
        if not self.pdf_path.get() or not self.excel_path.get() or not self.output_dir.get():
            messagebox.showerror("Error", "Please ensure PDF template, Excel file, and Output folder are selected.")
            return

        if not self.coords_pdf or not all(c is not None for c in self.coords_pdf):
            messagebox.showerror("Error", "Please select positions for all text columns defined from Excel.")
            return

        try:
            df = pd.read_excel(self.excel_path.get(), header=None)
            if df.shape[1] != self.num_excel_cols: # Consistency check
                messagebox.showerror("Error", "The number of columns in the Excel file has changed since initial load. Please reload.")
                return

            font_family_selected = self.font_family_var.get()
            font_size = self.font_size_var.get()

            if not font_family_selected:
                messagebox.showerror("Error", "Please select a font family.")
                return
            if font_size <= 0:
                messagebox.showerror("Error", "Font size must be positive.")
                return

            try:
                font_path = fm.findfont(font_family_selected)
            except Exception as e: # More general exception if findfont fails unexpectedly
                messagebox.showerror("Font File Error", f"Could not find the font file for '{font_family_selected}'.\nTry selecting a different font.\nError: {e}")
                self.status_label.config(text=f"Error: Font file not found for {font_family_selected}")
                return

            # Load font once for metrics and use in insert_text
            try:
                fitz_font = fitz.Font(fontname=font_family_selected, fontfile=font_path)
            except Exception as e:
                messagebox.showerror("Font Load Error", f"Could not load the font '{font_family_selected}' from path '{font_path}'.\n{e}")
                return

            self.status_label.config(text="Processing files...")
            self.master.update_idletasks() # Update GUI
            
            num_files_generated = 0 # Initialize counter for generated files
            for index, row in df.iterrows():
                doc_copy = fitz.open(self.pdf_path.get())
                page_to_modify = doc_copy.load_page(0) # Text injection still targets first page only as per original design

                for i in range(self.num_excel_cols):
                    if i >= row.size or i >= len(self.coords_pdf) or self.coords_pdf[i] is None or i >= len(self.is_rtl_vars):
                        continue # Skip if data for this column is missing or not configured

                    val = str(row.iloc[i]) if pd.notna(row.iloc[i]) else ""
                    is_rtl_output = self.is_rtl_vars[i].get()
                    current_coord_pdf = self.coords_pdf[i]

                    self._insert_text_on_pdf_page(page_to_modify,
                                                  val,
                                                  current_coord_pdf,
                                                  font_family_selected,
                                                  font_path,
                                                  font_size,
                                                  is_rtl_output,
                                                  fitz_font)

                output_filename = os.path.join(self.output_dir.get(), f"output_pdf_{index + 1}.pdf")
                doc_copy.save(output_filename)
                doc_copy.close()
                num_files_generated += 1

            self.status_label.config(text=f"Finished generating {num_files_generated} PDF files in: {self.output_dir.get()}")
            messagebox.showinfo("Success", f"{num_files_generated} PDF files generated successfully!")

        except Exception as e:
            self.status_label.config(text="Error during file generation.")
            messagebox.showerror("Processing Error", str(e))

    def generate_single_preview_pdf(self):
        if self.signature_mode_active.get():
            # This button's command is changed to self.generate_signed_pdf in signature mode
            self.generate_signed_pdf()
            return
        if not self.pdf_path.get():
            messagebox.showerror("Error", "Please load a PDF template file first.")
            return
        if self.excel_data_preview is None or self.excel_data_preview.empty:
            messagebox.showerror("Error", "Please load an Excel file with data first.")
            return
        if not self.output_dir.get(): # Need an output dir for the save dialog's initial dir
            messagebox.showerror("Error", "Please select an output folder first (to save the current file).")
            return
        if not self.coords_pdf or not all(c is not None for c in self.coords_pdf):
            messagebox.showerror("Error", "Please select positions for all text columns defined from Excel.")
            return

        current_row_idx = self.preview_row_index.get()
        if not (0 <= current_row_idx < self.excel_data_preview.shape[0]):
            messagebox.showerror("Error", "Invalid row selected for preview.")
            return

        font_family_selected = self.font_family_var.get()
        font_size = self.font_size_var.get()

        if not font_family_selected:
            messagebox.showerror("Error", "Please select a font family.")
            return
        if font_size <= 0:
            messagebox.showerror("Error", "Font size must be positive.")
            return

        try:
            font_path = fm.findfont(font_family_selected)
            fitz_font = fitz.Font(fontname=font_family_selected, fontfile=font_path)
        except Exception as e:
            messagebox.showerror("Font Error", f"Could not load the font '{font_family_selected}'.\n{e}")
            return

        output_filepath = filedialog.asksaveasfilename(
            initialdir=self.output_dir.get(),
            title="Save current PDF As",
            defaultextension=".pdf",
            filetypes=(("PDF files", "*.pdf"), ("All files", "*.*"))
        )

        if not output_filepath: # User cancelled save dialog
            return

        try:
            self.status_label.config(text="Generating current PDF...")
            self.master.update_idletasks()

            row_data = self.excel_data_preview.iloc[current_row_idx]
            
            doc_copy = fitz.open(self.pdf_path.get())
            page_to_modify = doc_copy.load_page(0) # Text injection still targets first page only

            for i in range(self.num_excel_cols):
                if i >= row_data.size or i >= len(self.coords_pdf) or self.coords_pdf[i] is None or i >= len(self.is_rtl_vars):
                    continue

                val = str(row_data.iloc[i]) if pd.notna(row_data.iloc[i]) else ""
                is_rtl_output = self.is_rtl_vars[i].get()
                current_coord_pdf = self.coords_pdf[i]

                self._insert_text_on_pdf_page(page_to_modify,
                                              val,
                                              current_coord_pdf,
                                              font_family_selected,
                                              font_path,
                                              font_size,
                                              is_rtl_output,
                                              fitz_font)

            doc_copy.save(output_filepath)
            doc_copy.close()
            self.status_label.config(text=f"current PDF saved to: {output_filepath}")
            messagebox.showinfo("Success", f"current PDF saved successfully!")
        except Exception as e:
            self.status_label.config(text="Error generating current PDF.")
            messagebox.showerror("Error Generating current PDF", str(e))

    # --- Signature Mode Methods ---
    def load_signature_image_prompt(self):
        if not self.pdf_doc:
            messagebox.showerror("Error", "Please load a PDF file first.")
            return
        path = filedialog.askopenfilename(
            title="Select Signature Image File",
            filetypes=(("Image files", "*.png *.jpg *.jpeg *.bmp *.gif *.tiff"), ("All files", "*.*"))
        )
        if not path:
            return
        try:
            pil_image = Image.open(path)
            pil_image.load() # Ensure image data is loaded immediately
            display_name = os.path.basename(path)
            self.loaded_signature_pil_images.append((pil_image, path, display_name))
            # References to self.loaded_signatures_listbox removed as the listbox itself was removed.
            self.status_label.config(text=f"Signature image '{display_name}' loaded. Select it and click on the PDF to place.")
        except Exception as e:
            messagebox.showerror("Error Loading Image", f"Could not load image: {path}\n{e}")
        
        # Automatically set the newly loaded signature as active for placement
        if self.loaded_signature_pil_images:
            new_idx = len(self.loaded_signature_pil_images) - 1
            self.active_signature_pil_idx_to_place.set(new_idx)
            # # print(f"DEBUG: load_signature_image_prompt: active_signature_pil_idx_to_place set to {new_idx}")
            self._build_dynamic_coord_controls() # Refresh sidebar
            # Default size for placement is handled in _execute_place_signature_at_click

    def apply_size_to_selected_signature(self):
        # This method is now obsolete due to drag-to-resize
        selected_idx = self.selected_placed_signature_idx.get()
        if selected_idx == -1 or selected_idx >= len(self.placed_signatures_data):
            messagebox.showerror("Error", "Please select a placed signature on the document first.")
            return
        
        sig_data = self.placed_signatures_data[selected_idx]
        try:
            # new_width_pt = self.signature_width_var.get() # Variable removed
            new_width_pt = DEFAULT_SIGNATURE_WIDTH_PT # Or some other logic if needed
            if new_width_pt <= 0:
                messagebox.showerror("Error", "Signature width must be positive.")
                return
            
            new_height_pt = new_width_pt / sig_data['aspect_ratio']
            # sig_data['pdf_rect_pts'].x1 = sig_data['pdf_rect_pts'].x0 + new_width_pt # Logic moved to resize handlers
            # sig_data['pdf_rect_pts'].y1 = sig_data['pdf_rect_pts'].y0 + new_height_pt
            # self.signature_height_var.set(round(new_height_pt,2)) # Variable removed
            # self._draw_placed_signatures() # Redraws images and then calls _redraw_selection_highlights()
            self.status_label.config(text="Signature size updated.")
        except tk.TclError:
            messagebox.showerror("Error", "Invalid width value.")
        except Exception as e:
            messagebox.showerror("Error", f"Error updating size: {e}")

    def delete_selected_placed_signature(self):
        selected_idx = self.selected_placed_signature_idx.get()
        if selected_idx == -1 or selected_idx >= len(self.placed_signatures_data):
            messagebox.showinfo("Info", "Please select a placed signature on the document to delete.")
            return
        
        try:
            del self.placed_signatures_data[selected_idx]
            self.selected_placed_signature_idx.set(-1) # Deselect
            self._draw_placed_signatures() # Redraws images and then calls _redraw_selection_highlights()
            self._build_dynamic_coord_controls() # Update sidebar
            self.status_label.config(text="Selected signature deleted.")
        except IndexError:
            # Should not happen if selected_idx check passes, but as a safeguard
            messagebox.showerror("Error", "Internal error: Could not find selected signature to delete.")

    def _on_delete_key_press(self, event):
        """Handles the Delete key press to delete the selected placed signature."""
        if self.signature_mode_active.get():
            selected_idx = self.selected_placed_signature_idx.get()
            if selected_idx != -1 and 0 <= selected_idx < len(self.placed_signatures_data):
                # Optionally, add a confirmation dialog here
                # if messagebox.askyesno("Confirm Delete", "Are you sure you want to delete the selected signature?"):
                self.delete_selected_placed_signature()

    def generate_signed_pdf(self):
        if not self.pdf_path.get() or not self.pdf_doc:
            messagebox.showerror("Error", "Please load a PDF file first.")
            return
        if not self.placed_signatures_data:
            messagebox.showerror("Error", "Please place at least one signature on the document.")
            return
        # Removed: Output directory check, as we will use asksaveasfilename

        initial_dir_for_save = self.output_dir.get() # Try to use it if set (e.g. user switched from text mode)
        if not initial_dir_for_save: # If not set (e.g. started in sig mode)
            if self.pdf_path.get(): # Use PDF's directory if available
                initial_dir_for_save = os.path.dirname(self.pdf_path.get())
            else: # Fallback to user's home directory
                initial_dir_for_save = os.path.expanduser("~")

        output_filepath = filedialog.asksaveasfilename(
            initialdir=initial_dir_for_save, title="Save Signed PDF As",
            defaultextension=".pdf", filetypes=(("PDF files", "*.pdf"), ("All files", "*.*"))
        )
        if not output_filepath: return

        try:
            self.status_label.config(text="Creating signed PDF...")
            self.master.update_idletasks()
            
            doc_to_sign = fitz.open(self.pdf_path.get()) # Open fresh copy of original PDF

            for placed_sig_data in self.placed_signatures_data:
                pil_idx = placed_sig_data['pil_image_idx']
                _, image_file_path, _ = self.loaded_signature_pil_images[pil_idx]
                pdf_rect = placed_sig_data['pdf_rect_pts'] # This is already in PDF points, y from top

                for page_num in range(doc_to_sign.page_count):
                    page = doc_to_sign.load_page(page_num)
                    # insert_image uses rect where y0 is top, y1 is bottom. Our pdf_rect_pts is already like that.
                    page.insert_image(pdf_rect, filename=image_file_path, keep_proportion=True, overlay=True)
            
            doc_to_sign.save(output_filepath, garbage=4, deflate=True) # Save with options
            doc_to_sign.close()
            self.status_label.config(text=f"Signed PDF saved to: {output_filepath}")
            messagebox.showinfo("Success", "Signed PDF created and saved successfully!")

        except Exception as e:
            self.status_label.config(text="Error creating signed PDF.")
            messagebox.showerror("Error Creating Signed PDF", f"Error creating signed PDF: {e}")

    # Helper for signature rect conversion
    def _pdf_rect_to_canvas_rect_params(self, pdf_rect_pts: fitz.Rect):
        # pdf_rect_pts is {x0,y0,x1,y1} in PDF points, y from top
        # Returns (canvas_x_tl, canvas_y_tl, canvas_w, canvas_h)
        if not self.pdf_doc or self.pdf_page_width_pt == 0 or self.pdf_page_height_pt == 0 or \
           self.image_on_canvas_width_px == 0 or self.image_on_canvas_height_px == 0 : # Added check for canvas image dims
            return None

        # Convert PDF top-left to canvas top-left
        canvas_x_tl = (pdf_rect_pts.x0 / self.pdf_page_width_pt) * self.image_on_canvas_width_px
        canvas_y_tl = (pdf_rect_pts.y0 / self.pdf_page_height_pt) * self.image_on_canvas_height_px
        
        # Convert PDF width/height to canvas width/height
        pdf_w = pdf_rect_pts.width
        pdf_h = pdf_rect_pts.height
        canvas_w = (pdf_w / self.pdf_page_width_pt) * self.image_on_canvas_width_px
        canvas_h = (pdf_h / self.pdf_page_height_pt) * self.image_on_canvas_height_px
        
        return canvas_x_tl, canvas_y_tl, canvas_w, canvas_h

    def _canvas_pos_to_pdf_pos_tl(self, canvas_x, canvas_y):
        # Converts a canvas top-left click coordinate to PDF top-left coordinate (points, y from top)
        if not self.pdf_doc or self.image_on_canvas_width_px == 0 or self.image_on_canvas_height_px == 0:
            return None

        pdf_x_pt = (canvas_x / self.image_on_canvas_width_px) * self.pdf_page_width_pt
        pdf_y_pt = (canvas_y / self.image_on_canvas_height_px) * self.pdf_page_height_pt
        return pdf_x_pt, pdf_y_pt

    # --- Resize Handle Methods ---
    def _on_resize_handle_enter(self, event):
        item_id = self.canvas.find_withtag(tk.CURRENT)
        if not item_id: return
        tags = self.canvas.gettags(item_id[0])
        # Determine cursor based on handle type (e.g., "handle_tl", "handle_br")
        # For simplicity, using "sizing" for all now. More specific cursors can be added.
        # e.g. if "handle_tl" in tags or "handle_br" in tags: self.canvas.config(cursor="size_nw_se")
        #      elif "handle_tr" in tags or "handle_bl" in tags: self.canvas.config(cursor="size_ne_sw")
        self.canvas.config(cursor="sizing")
        self.canvas.itemconfig(item_id[0], fill=RESIZE_HANDLE_ACTIVE_COLOR)

    def _on_resize_handle_leave(self, event):
        item_id = self.canvas.find_withtag(tk.CURRENT) # Or check event.widget if it's the handle itself
        # Only reset cursor if not actively resizing OR if the item left is not the one being resized
        is_active_resize_on_this_handle = False
        if self._resize_data["active"] and item_id:
            tags = self.canvas.gettags(item_id[0])
            if f"handle_sig_{self._resize_data['sig_idx']}" in tags and f"handle_{self._resize_data['handle_type']}" in tags:
                is_active_resize_on_this_handle = True
        
        if not is_active_resize_on_this_handle:
            self.canvas.config(cursor="")
            if item_id: # Reset color of the specific handle that was left
                self.canvas.itemconfig(item_id[0], fill=RESIZE_HANDLE_COLOR)


    def _on_resize_handle_press(self, event):
        item_tuple = self.canvas.find_withtag(tk.CURRENT)
        if not item_tuple: return "break"
        item_id = item_tuple[0]
        tags = self.canvas.gettags(item_id)

        sig_idx = -1
        handle_type = None
        for tag in tags:
            if tag.startswith("handle_sig_"):
                sig_idx = int(tag.split("_")[2])
            elif tag.startswith("handle_") and not tag.startswith("handle_sig_"):
                handle_type = tag.split("_")[1] # "tl", "tr", "br", "bl"
        
        if sig_idx != -1 and handle_type and 0 <= sig_idx < len(self.placed_signatures_data):
            # # print(f"DEBUG RESIZE PRESS: Matched sig_idx={sig_idx}, handle={handle_type}. Setting resize active.")
            self._select_placed_signature(sig_idx, from_press_event=True) # Ensure it's selected
            sig_data = self.placed_signatures_data[sig_idx]
            self._resize_data["active"] = True
            self._resize_data["sig_idx"] = sig_idx
            self._resize_data["handle_type"] = handle_type
            self._resize_data["start_mouse_x_canvas"] = self.canvas.canvasx(event.x)
            self._resize_data["start_mouse_y_canvas"] = self.canvas.canvasy(event.y)
            self._resize_data["original_pdf_rect"] = fitz.Rect(sig_data['pdf_rect_pts'].x0, sig_data['pdf_rect_pts'].y0, sig_data['pdf_rect_pts'].x1, sig_data['pdf_rect_pts'].y1)
            self._resize_data["aspect_ratio"] = sig_data['aspect_ratio']
            self._item_drag_active = True # Prevent panning and other B1 canvas actions
            return "break" # Consume the event

if __name__ == "__main__":
    root = tk.Tk()
    default_font = tkFont.nametofont("TkDefaultFont")
    default_font.configure(family="Arial", size=10)
    root.option_add("*Font", default_font)
 
    app = PDFBatchApp(root)
    root.mainloop()