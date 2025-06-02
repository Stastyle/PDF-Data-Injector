## PDFDataInjector.py
# A Tkinter application to inject data from an Excel file into a PDF template.
# It allows users to select a PDF template, an Excel data file, and an output directory, # type: ignore
# and dynamically place text fields on the PDF based on the Excel data.
# The application supports zooming, panning, and RTL text handling for Hebrew text.
# It also provides a preview of the PDF with the injected data.
# and _on_canvas_b1_motion.
# UI_LANGUAGE: English. All user-facing strings should be in English.
# If a marker was being dragged, it will be handled by the marker's own bindings. # type: ignore
# version number should be increased with each generated iteration by 0.01.
# version 1.40

import tkinter as tk
from tkinter import filedialog, messagebox, font as tkFont, simpledialog, ttk
import customtkinter # Added for CustomTkinter
import pandas as pd
import fitz  # PyMuPDF
import os
# import arabic_reshaper # Not directly used in the provided snippet, but kept if used by get_display
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
TEXT_ALIGNMENTS = ["left", "center", "right"] # For text alignment
DEFAULT_PDF_TEXT_COLOR = (0, 0, 0) # Black
OPERATION_MODES = ["Text Injection", "Signature Mode"]

class PDFBatchApp:
    def __init__(self, master):
        self.master = master # This will be a customtkinter.CTk() instance
        master.title("PDF Data Injector")
        master.geometry("1300x900") # Increased height for preview

        # --- CustomTkinter Theme Settings ---
        # customtkinter.set_appearance_mode("System") # Handled in __main__
        # customtkinter.set_default_color_theme("blue") # Handled in __main__

        # --- Variables ---
        self.pdf_path = tk.StringVar()
        self.excel_path = tk.StringVar()
        self.output_dir = tk.StringVar()
        # StringVars for displaying only filenames/directory names
        self.pdf_display_var = tk.StringVar(value="(No file selected)")
        self.excel_display_var = tk.StringVar(value="(No file selected)")
        self.output_dir_display_var = tk.StringVar(value="(No folder selected)")
        self.include_header_row = tk.BooleanVar(value=False) # Default: Exclude header row
        self.font_family_var = tk.StringVar() 
        # self.font_size_var = tk.IntVar(value=12) # Default font size - Will be per-column now
        self.excel_preview_text = tk.StringVar(value="Excel Preview: (Load Excel file)") # For internal data, not displayed directly
        self.current_zoom_factor = tk.DoubleVar(value=1.0)
        self.zoom_display_var = tk.StringVar(value="Zoom: 100%")
        self.preview_row_index = tk.IntVar(value=0) # 0-based index for preview row
        
        # --- PDF Page Navigation Variables ---
        self.current_pdf_page_num = tk.IntVar(value=0)
        self.pdf_total_pages = tk.IntVar(value=0)
        self.pdf_page_display_var = tk.StringVar(value="Page: -/-")
        self.preview_row_display = tk.StringVar(value="Row: -")
        self.operation_mode_var = tk.StringVar(value=OPERATION_MODES[0]) # Default to Text Injection
        self.managed_columns = [] # List of dicts: {'original_excel_col_idx': int, 'display_name': str, 'unique_id': str}
        
        self.is_rtl_vars = [] # List of tk.BooleanVar for RTL status of each column
        self.col_status_vars = [] # List of tk.StringVar for V/X status of each column
        self.col_alignment_vars = [] # List of tk.StringVar for text alignment of each column
        self.col_font_size_vars = [] # List of tk.IntVar for font size of each managed column

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
            "handle_type": None, # e.g., "tl", "tr", "br", "bl"משה
            "start_mouse_x_canvas": 0, # Canvas coords
            "start_mouse_y_canvas": 0, # Canvas coords
            "original_pdf_rect": None, # fitz.Rect of the signature at drag start (PDF points, y from top)
            "canvas_item_id_sig": None, 
            "aspect_ratio": 1.0
        }
        self._zoom_debounce_timer = None
        self._DEBOUNCE_TIME_MS = 10 # Milliseconds to wait before applying zoom (reduced from 75 for responsiveness)

        # --- GUI Layout ---
        # Main application frame
        self.main_app_frame = customtkinter.CTkFrame(master, corner_radius=0)
        self.main_app_frame.pack(fill=tk.BOTH, expand=True)

        # --- Create PanedWindow for resizable left/right panels ---
        sash_color = self._get_paned_window_sash_color() # Initial sash color

        self.paned_window = tk.PanedWindow(
            self.main_app_frame,
            orient=tk.HORIZONTAL,
            sashwidth=6,          # Width of the sash
            sashrelief=tk.FLAT,   # Relief of the sash
            bd=0,                 # Borderwidth for the PanedWindow itself
            bg=sash_color,        # Background color of the sash
            opaqueresize=True     # Resize content during drag
        )
        self.paned_window.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # Create intermediate frames for the PanedWindow
        self.left_pane_content_frame = customtkinter.CTkFrame(self.paned_window, fg_color="transparent")
        self.right_pane_content_frame = customtkinter.CTkFrame(self.paned_window, fg_color="transparent")

        # Left panel for all controls (potentially scrollable)
        # Now a child of the intermediate left_pane_content_frame
        self.left_controls_panel = customtkinter.CTkScrollableFrame(self.left_pane_content_frame) 
        self.left_controls_panel.pack(fill=tk.BOTH, expand=True)

        # Right panel for PDF display
        self.right_pdf_panel = customtkinter.CTkFrame(self.right_pane_content_frame, fg_color="transparent")
        self.right_pdf_panel.pack(fill=tk.BOTH, expand=True)


        # --- Theme Toggle Button ---
        self.theme_button = customtkinter.CTkButton(self.left_controls_panel, text="Toggle Theme", command=self._toggle_theme)
        self.theme_button.pack(fill=tk.X, padx=5, pady=(5,10))

        # --- Operation Mode Selection ---
        self.mode_selection_frame = customtkinter.CTkFrame(self.left_controls_panel)
        self.mode_selection_frame.pack(fill=tk.X, padx=5, pady=5)
        customtkinter.CTkLabel(self.mode_selection_frame, text="Operation Mode:").pack(side=tk.LEFT, padx=(5,5))
        self.mode_combo = customtkinter.CTkComboBox(self.mode_selection_frame, variable=self.operation_mode_var, values=OPERATION_MODES, state="readonly", command=self._on_operation_mode_dropdown_change)
        self.mode_combo.pack(side=tk.LEFT, padx=(0,5), expand=True, fill=tk.X)

        # --- PDF Selection Frame ---
        self.pdf_selection_frame = customtkinter.CTkFrame(self.left_controls_panel)
        self.pdf_selection_frame.pack(fill=tk.X, padx=5, pady=5)
        customtkinter.CTkLabel(self.pdf_selection_frame, text="PDF Template:").grid(row=0, column=0, sticky="w", padx=5, pady=2)
        customtkinter.CTkButton(self.pdf_selection_frame, text="Select PDF", command=self.load_pdf_template, width=100).grid(row=1, column=0, padx=5, pady=2, sticky="ew")
        self.pdf_display_entry = customtkinter.CTkEntry(self.pdf_selection_frame, textvariable=self.pdf_display_var, width=180, state="disabled")
        self.pdf_display_entry.grid(row=1, column=1, padx=5, pady=2, sticky="ew")
        self.pdf_selection_frame.grid_columnconfigure(1, weight=1) # Allow entry to expand

        # --- Text Injection Controls (will be hidden in signature mode) ---
        # Excel Selection
        self.excel_selection_frame = customtkinter.CTkFrame(self.left_controls_panel)
        # Packed/unpacked by _on_signature_mode_change
        customtkinter.CTkLabel(self.excel_selection_frame, text="Excel Data File:").grid(row=0, column=0, sticky="w", padx=5, pady=2)
        customtkinter.CTkButton(self.excel_selection_frame, text="Select Excel", command=self.load_excel_data, width=100).grid(row=1, column=0, padx=5, pady=2, sticky="ew")
        self.excel_display_entry = customtkinter.CTkEntry(self.excel_selection_frame, textvariable=self.excel_display_var, width=180, state="disabled")
        self.excel_display_entry.grid(row=1, column=1, padx=5, pady=2, sticky="ew")
        self.excel_selection_frame.grid_columnconfigure(1, weight=1)

        # Option to include/exclude header row
        self.header_row_frame = customtkinter.CTkFrame(self.left_controls_panel)
        # Packed/unpacked by _on_signature_mode_change
        customtkinter.CTkCheckBox(self.header_row_frame, text="Include first row (header) in output", variable=self.include_header_row).pack(padx=5, pady=5, anchor="w")

        # Output Directory Selection
        self.output_dir_frame = customtkinter.CTkFrame(self.left_controls_panel)
        # Packed/unpacked by _on_signature_mode_change
        customtkinter.CTkLabel(self.output_dir_frame, text="Output Folder:").grid(row=0, column=0, sticky="w", padx=5, pady=2)
        customtkinter.CTkButton(self.output_dir_frame, text="Select Folder", command=self.select_output_dir, width=100).grid(row=1, column=0, padx=5, pady=2, sticky="ew")
        self.output_dir_display_entry = customtkinter.CTkEntry(self.output_dir_frame, textvariable=self.output_dir_display_var, width=180, state="disabled")
        self.output_dir_display_entry.grid(row=1, column=1, padx=5, pady=2, sticky="ew")
        self.output_dir_frame.grid_columnconfigure(1, weight=1)

        # Font Selection
        self.font_controls_frame = customtkinter.CTkFrame(self.left_controls_panel)
        # Packed/unpacked by _on_signature_mode_change
        customtkinter.CTkLabel(self.font_controls_frame, text="Font Family:").pack(side=tk.TOP, anchor="w", padx=5, pady=(5,0))
        font_details_subframe = customtkinter.CTkFrame(self.font_controls_frame, fg_color="transparent")
        font_details_subframe.pack(fill=tk.X, padx=0, pady=0)
        
        # Populate font families
        font_families = sorted(list(tkFont.families()))
        self.font_combo = customtkinter.CTkComboBox(font_details_subframe, variable=self.font_family_var, values=font_families, width=180, state="readonly")
        if "Arial" in font_families:
            self.font_family_var.set("Arial") # Default font
        elif font_families:
            self.font_family_var.set(font_families[0]) # Fallback to first available font
        self.font_combo.pack(side=tk.LEFT, padx=(5,2), pady=2)

        customtkinter.CTkLabel(font_details_subframe, text="Size:").pack(side=tk.LEFT, padx=(10, 2), pady=2)
        # Global font size entry and buttons are removed. Will be per-column.
        # self.font_size_entry = customtkinter.CTkEntry(font_details_subframe, textvariable=self.font_size_var, width=40)
        # self.font_size_entry.pack(side=tk.LEFT, padx=(0,2), pady=2)
        # customtkinter.CTkButton(font_details_subframe, text="-", command=lambda: self._adjust_font_size(-1), width=25).pack(side=tk.LEFT, padx=(0,2), pady=2)
        # customtkinter.CTkButton(font_details_subframe, text="+", command=lambda: self._adjust_font_size(1), width=25).pack(side=tk.LEFT, padx=(0,5), pady=2)
        customtkinter.CTkLabel(font_details_subframe, text="(Per-field size below)").pack(side=tk.LEFT, padx=(5,0))

        # --- Zoom Controls ---
        self.zoom_frame = customtkinter.CTkFrame(self.left_controls_panel)
        self.zoom_frame.pack(fill=tk.X, padx=5, pady=5)
        customtkinter.CTkLabel(self.zoom_frame, text="Zoom:").pack(side=tk.LEFT, padx=(5,0))
        customtkinter.CTkButton(self.zoom_frame, text="-", command=lambda: self.zoom(-0.2), width=30).pack(side=tk.LEFT, padx=2)
        customtkinter.CTkLabel(self.zoom_frame, textvariable=self.zoom_display_var).pack(side=tk.LEFT, padx=5)
        customtkinter.CTkButton(self.zoom_frame, text="+", command=lambda: self.zoom(0.2), width=30).pack(side=tk.LEFT, padx=2)
        
        # --- Text Preview Row Controls ---
        self.text_row_preview_frame = customtkinter.CTkFrame(self.left_controls_panel)
        # Packed/unpacked by _on_signature_mode_change
        customtkinter.CTkLabel(self.text_row_preview_frame, text="Preview Row:").pack(side=tk.LEFT, padx=(5,0))
        self.prev_row_button = customtkinter.CTkButton(self.text_row_preview_frame, text="↑", command=lambda: self._change_preview_row(-1), state=tk.DISABLED, width=30)
        self.prev_row_button.pack(side=tk.LEFT, padx=(15,0)) 

        self.preview_row_label = customtkinter.CTkLabel(self.text_row_preview_frame, textvariable=self.preview_row_display, width=70) # width in pixels
        self.preview_row_label.pack(side=tk.LEFT, padx=2)

        self.next_row_button = customtkinter.CTkButton(self.text_row_preview_frame, text="↓", command=lambda: self._change_preview_row(1), state=tk.DISABLED, width=30)
        self.next_row_button.pack(side=tk.LEFT, padx=(0,5))

        self.toggle_text_preview_button = customtkinter.CTkButton(self.text_row_preview_frame, text="Show/Hide Preview", command=self.toggle_text_preview)
        self.toggle_text_preview_button.pack(side=tk.LEFT, padx=(10,0))

        # --- Generate Buttons Frame (Define earlier, pack later at the bottom) ---
        self.generate_buttons_frame = customtkinter.CTkFrame(self.left_controls_panel)
        # self.generate_buttons_frame.pack(side=tk.BOTTOM, fill=tk.X, padx=5, pady=(10,5)) # Packing moved to the end

        self.generate_all_pdfs_button = customtkinter.CTkButton(self.generate_buttons_frame, text="Generate PDF Files", command=self.generate_output_pdfs, font=("Arial", 12, "bold"), fg_color="#A6D8F0", text_color="black", hover_color="#8AC7E6")
        self.generate_current_pdf_button = customtkinter.CTkButton(self.generate_buttons_frame, text="Generate Current PDF", command=self.generate_single_preview_pdf)



        # --- Generate Buttons Frame ---

        # --- Column/Signature Controls Sidebar ---
        # This will be packed into left_controls_panel
        self.column_controls_sidebar = customtkinter.CTkFrame(self.left_controls_panel, border_width=1)
        # Packed/unpacked by _on_signature_mode_change, content built by _build_dynamic_coord_controls

        self.signature_mode_active.trace_add("write", self._on_signature_mode_change)

        # PDF Page Navigation Frame (below content_area, above status_label)
        self.pdf_nav_frame = customtkinter.CTkFrame(self.right_pdf_panel, fg_color="transparent") # Moved to right_pdf_panel
        # This frame will be packed later, only if a PDF is loaded.
        self.prev_pdf_page_button = customtkinter.CTkButton(self.pdf_nav_frame, text="< Prev Page", command=lambda: self._change_pdf_page(-1), state=tk.DISABLED, width=100)
        self.prev_pdf_page_button.pack(side=tk.LEFT, padx=5, pady=2)
        self.pdf_page_label = customtkinter.CTkLabel(self.pdf_nav_frame, textvariable=self.pdf_page_display_var, width=100) # width in pixels
        self.pdf_page_label.pack(side=tk.LEFT, padx=5, pady=2)
        self.next_pdf_page_button = customtkinter.CTkButton(self.pdf_nav_frame, text="Next Page >", command=lambda: self._change_pdf_page(1), state=tk.DISABLED, width=100)
        self.next_pdf_page_button.pack(side=tk.LEFT, padx=5, pady=2)

        # Status Label
        self.status_label = customtkinter.CTkLabel(self.right_pdf_panel, text="Please load a PDF template to begin.", anchor="w") # Moved to right_pdf_panel
        
        # Packing order for right_pdf_panel content
        self.canvas_container = customtkinter.CTkFrame(self.right_pdf_panel, border_width=1) # Replaces bd/relief
        self.canvas_container.pack(fill=tk.BOTH, expand=True, padx=0, pady=0) # Fill available space
        
        self.pdf_nav_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(0,2))
        self.pdf_nav_frame.pack_forget() # Initially hidden
        self.status_label.pack(side=tk.BOTTOM, fill=tk.X, pady=(2,0))
        
        # NOTE: tk.Canvas is used here as CustomTkinter does not have a direct equivalent
        # with the same rich drawing and event binding capabilities.
        # tk.Scrollbar is also used for compatibility with tk.Canvas.
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
        self.excel_selection_frame.pack_forget()
        self.output_dir_frame.pack_forget()
        self.font_controls_frame.pack_forget()
        self.text_row_preview_frame.pack_forget()
        self.generate_all_pdfs_button.pack_forget()
        self.column_controls_sidebar.pack_forget()

        # The generate_current_pdf_button's text and command will be set by _on_signature_mode_change
        # The column_controls_sidebar content is built by _build_dynamic_coord_controls, called by _on_signature_mode_change.
        self._on_signature_mode_change() # Call once to set initial state based on self.signature_mode_active


        # --- Pack Generate Buttons Frame (Packed last in left_controls_panel to be at the bottom) ---
        self.generate_buttons_frame.pack(side=tk.BOTTOM, fill=tk.X, padx=5, pady=(10,5)) # side=tk.BOTTOM

        # Add panels to PanedWindow
        self.paned_window.add(self.left_pane_content_frame, minsize=280)  # Add the intermediate frame
        self.paned_window.add(self.right_pane_content_frame, minsize=400) # Add the intermediate frame

        # Schedule setting the initial sash position after the window is mapped
        self.initial_sash_set_flag = False # Flag to ensure sash is set only once
        self.paned_window.bind("<Configure>", self._set_initial_sash_position_on_configure)

        # Apply initial theme colors to panels and canvas
        self._apply_theme_colors()
        # self.master.after(150, self._set_initial_sash_position) # Old method

    def _set_initial_sash_position_on_configure(self, event=None):
        if self.initial_sash_set_flag:
            return # Already set

        try:
            # update_idletasks might not be strictly necessary here as <Configure> implies readiness
            # but it doesn't hurt, and can help ensure winfo_width is current.
            self.paned_window.update_idletasks()
            pw_width = self.paned_window.winfo_width()
            master_width = self.master.winfo_width() # Get current master window width

            print(f"DEBUG: Configure event. MasterW: {master_width}, PaneW: {pw_width}, Flag: {self.initial_sash_set_flag}")

            # We set the sash if the PanedWindow's width is substantial.
            # Let's assume the PanedWindow should eventually be close to the master window's width.
            # We'll proceed if pw_width is at least, say, 70% of master_width, and also above an absolute minimum.
            # This helps ensure we're not acting on intermediate, small sizes during window creation.
            if pw_width > (master_width * 0.7) and pw_width > 800: # Heuristic: pw_width is significant
                # Calculate sash position as 40% of the current PanedWindow width
                sash_pos = int(pw_width * 0.40) # Changed to 30% for the left pane

                print(f"DEBUG: Attempting sash_place. pw_width={pw_width}, master_width={master_width}, calculated sash_pos={sash_pos}")

                # Ensure the calculated sash position respects the minsize of the left pane (280)
                # Also ensure that the remaining width for the right pane respects its minsize (400).
                # For paneconfigure, we calculate target_left_width and ensure it and the remainder meet minsizes.
                target_left_width = sash_pos # sash_pos is already calculated as pw_width * 0.40
                remaining_width_for_right = pw_width - target_left_width
                if target_left_width >= 280 and remaining_width_for_right >= 400:
                    # Revert to using paneconfigure, as sash_place might have issues
                    self.paned_window.paneconfigure(self.left_pane_content_frame, width=target_left_width)
                    self.paned_window.update_idletasks() # Ensure change is processed

                    self.initial_sash_set_flag = True
                    
                    # Check actual sash position after setting
                    actual_sash_coord = self.paned_window.sash_coord(0) # (x, y) of the sash
                    print(f"DEBUG: Sash position attempt. PaneW: {pw_width}, Target Left Width: {target_left_width}, Actual Sash Coord: {actual_sash_coord}. Unbinding.")
                    self.paned_window.unbind("<Configure>") # Unbind only after successful, satisfactory setting
                else:
                    print(f"DEBUG: Sash target {target_left_width} or remaining {remaining_width_for_right} (from pw_width {pw_width}) fails minsize. Deferring.")
            else:
                print(f"DEBUG: PaneW {pw_width} (MasterW {master_width}) not yet sufficient for primary condition. Deferring sash set.")
        except tk.TclError as e:
            if "invalid command name" not in str(e).lower(): # Avoid spam on window close
                print(f"Error setting initial sash position on configure (widget might be gone): {e}")
        except Exception as e: # Catch other potential errors, e.g. if master.winfo_width() is not ready early on
            print(f"Unexpected error in _set_initial_sash_position_on_configure: {e}")

    def _get_paned_window_sash_color(self):
        sash_color = "gray75"  # Default sash color
        try:
            current_theme_settings = customtkinter.ThemeManager.theme
            appearance_mode = customtkinter.get_appearance_mode()  # "Light" or "Dark"
            if "CTkFrame" in current_theme_settings and "border_color" in current_theme_settings["CTkFrame"]:
                theme_border_color = current_theme_settings["CTkFrame"]["border_color"]
                if isinstance(theme_border_color, tuple) and len(theme_border_color) == 2:
                    sash_color = theme_border_color[1] if appearance_mode == "Dark" else theme_border_color[0]
                elif isinstance(theme_border_color, str):
                    sash_color = theme_border_color
            elif appearance_mode == "Dark":
                sash_color = "gray40"
            else: # Light
                sash_color = "gray75"
        except Exception:
            pass  # Use default if theme access fails
        return sash_color

    def _update_paned_window_sash_color(self):
        sash_color = self._get_paned_window_sash_color()
        self.paned_window.configure(bg=sash_color)

    def _apply_theme_colors(self):
        current_mode = customtkinter.get_appearance_mode()
        
        # Get the fg_color definition for CTkFrame from the theme
        # Expected: tuple/list (light_color, dark_color) or a single color string.
        # Problematic case observed: a single string "light_color dark_color"
        theme_fg_color_setting = customtkinter.ThemeManager.theme["CTkFrame"]["fg_color"]

        actual_light_color = None
        actual_dark_color = None

        if isinstance(theme_fg_color_setting, (tuple, list)) and len(theme_fg_color_setting) == 2:
            actual_light_color = str(theme_fg_color_setting[0])
            actual_dark_color = str(theme_fg_color_setting[1])
        elif isinstance(theme_fg_color_setting, str):
            parts = theme_fg_color_setting.split()
            if len(parts) == 2: # Attempt to parse "light_color dark_color" string
                print(f"Warning: CTkFrame fg_color from theme is a single string with two parts: '{theme_fg_color_setting}'. Parsing as light='{parts[0]}', dark='{parts[1]}'.")
                actual_light_color = parts[0]
                actual_dark_color = parts[1]
            elif len(parts) == 1: # Single valid color string
                actual_light_color = theme_fg_color_setting
                actual_dark_color = theme_fg_color_setting
            # else: parts is empty or > 2, will be handled by fallbacks
        
        # Fallbacks if parsing failed or colors are still invalid (e.g. contain spaces)
        # Use CTk's default frame colors as a safe fallback.
        # Example: customtkinter.ThemeManager.theme["CTk"]["fg_color"] is often ["gray92", "gray14"]
        default_theme_colors = customtkinter.ThemeManager.theme.get("CTk", {}).get("fg_color")
        if not (isinstance(default_theme_colors, (list, tuple)) and len(default_theme_colors) == 2):
            default_theme_colors = ["gray92", "gray14"] # Absolute fallback

        safe_light_fallback = str(default_theme_colors[0])
        safe_dark_fallback = str(default_theme_colors[1])

        if not actual_light_color or not isinstance(actual_light_color, str) or ' ' in actual_light_color:
            print(f"Warning: Parsed light color '{actual_light_color}' is invalid. Using fallback: {safe_light_fallback}")
            actual_light_color = safe_light_fallback
        if not actual_dark_color or not isinstance(actual_dark_color, str) or ' ' in actual_dark_color:
            print(f"Warning: Parsed dark color '{actual_dark_color}' is invalid. Using fallback: {safe_dark_fallback}")
            actual_dark_color = safe_dark_fallback
            
        # Assign panel and canvas colors based on the reliably parsed single color strings
        panel_bg_color_to_set = None
        canvas_bg_color_to_set = None

        if current_mode == "Dark":
            panel_bg_color_to_set = actual_dark_color
            canvas_bg_color_to_set = actual_dark_color # Canvas matches panel in dark mode
        else:  # Light Mode
            panel_bg_color_to_set = actual_light_color
            canvas_bg_color_to_set = "lightgrey" # Canvas is lightgrey in light mode as per original design

        self.right_pdf_panel.configure(fg_color=panel_bg_color_to_set)
        self.canvas_container.configure(fg_color=panel_bg_color_to_set) 
        self.canvas.configure(bg=canvas_bg_color_to_set)

        self._update_paned_window_sash_color()

    def _toggle_theme(self):
        current_mode = customtkinter.get_appearance_mode()
        if current_mode == "Light":
            customtkinter.set_appearance_mode("Dark")
        else:
            customtkinter.set_appearance_mode("Light")
        self._apply_theme_colors()

    def _on_operation_mode_dropdown_change(self, choice):
        # This function is called when the ComboBox selection changes.
        # The 'choice' argument is the new value of the ComboBox.
        if choice == OPERATION_MODES[1]: # "Signature Mode"
            self.signature_mode_active.set(True)
        else: # "Text Injection"
            self.signature_mode_active.set(False)
        # The trace on self.signature_mode_active will call _on_signature_mode_change
    def _on_signature_mode_change(self, *args):
        is_sig_mode = self.signature_mode_active.get()
        if is_sig_mode:
            self.status_label.configure(text="Signature mode active. Load a signature image and place it on the document.")
            # Hide text injection controls
            self.excel_selection_frame.pack_forget()
            self.output_dir_frame.pack_forget()
            self.font_controls_frame.pack_forget()
            self.header_row_frame.pack_forget() # Hide header option
            self.text_row_preview_frame.pack_forget()
            self.column_controls_sidebar.pack_forget() # Hide column sidebar
            self.generate_all_pdfs_button.pack_forget() # Hide batch generate
            self.generate_current_pdf_button.configure(text="Create Signed PDF", command=self.generate_signed_pdf)
            self.generate_current_pdf_button.pack(side=tk.RIGHT) # Ensure it's packed

            if self.operation_mode_var.get() != OPERATION_MODES[1]: # Sync dropdown if changed by other means
                self.operation_mode_var.set(OPERATION_MODES[1])
            
            # Ensure text-specific preview controls are hidden
            self.prev_row_button.pack_forget()
            self.preview_row_label.pack_forget()
            self.next_row_button.pack_forget() # These are part of text_row_preview_frame
            self.toggle_text_preview_button.pack_forget() # These are part of text_row_preview_frame
            
            # Clear text-related previews and data
            self.excel_data_preview = None
            self.coords_pdf = []
            self.num_excel_cols = 0
            self.managed_columns.clear()
            self._update_text_preview() # Clears text preview
            self._draw_markers() # Clears markers
            self.excel_display_var.set("(N/A in Signature Mode)")
            self.column_controls_sidebar.pack(fill=tk.BOTH, expand=True, padx=5, pady=5) # Ensure sidebar is visible

        else: # Text injection mode
            self.status_label.configure(text="Text injection mode. Load PDF, Excel and define positions.")
            # Show text injection controls
            self.excel_selection_frame.pack(fill=tk.X, padx=5, pady=5)
            self.output_dir_frame.pack(fill=tk.X, padx=5, pady=5)
            self.font_controls_frame.pack(fill=tk.X, padx=5, pady=5)
            self.header_row_frame.pack(fill=tk.X, padx=5, pady=5) # Show header option
            self.text_row_preview_frame.pack(fill=tk.X, padx=5, pady=5)
            self.column_controls_sidebar.pack(fill=tk.BOTH, expand=True, padx=5, pady=5) # Show column sidebar
            
            # Ensure correct buttons are shown in generate_buttons_frame
            self.generate_all_pdfs_button.pack(side=tk.RIGHT, padx=(5,0))
            self.generate_current_pdf_button.pack(side=tk.RIGHT) # Ensure it's packed
            self.generate_current_pdf_button.configure(text="Generate Current PDF", command=self.generate_single_preview_pdf)
            # Ensure text-specific preview controls (already packed within text_row_preview_frame)
            # self.prev_row_button.pack(side=tk.LEFT, padx=(15,0))
            # self.preview_row_label.pack(side=tk.LEFT, padx=2)
            # self.next_row_button.pack(side=tk.LEFT, padx=(0,5))
            # self.toggle_text_preview_button.pack(side=tk.LEFT, padx=(10,0))

            if self.operation_mode_var.get() != OPERATION_MODES[0]: # Sync dropdown
                self.operation_mode_var.set(OPERATION_MODES[0])
            
            # Clear signature data
            self.loaded_signature_pil_images = []
            self.placed_signatures_data = []
            self.active_signature_pil_idx_to_place.set(-1)
            self.selected_placed_signature_idx.set(-1)
            self._draw_placed_signatures() # Clears signature previews
            self.managed_columns.clear() # Clear managed columns when switching away from text mode
            self.coords_pdf.clear()      # Clear associated coords
            if self.pdf_doc: # If PDF is loaded, ensure page nav is visible
                self._redisplay_pdf_page() 
        self._build_dynamic_coord_controls() # Rebuild sidebar for the current mode
    def _bind_variables(self): # Renamed
        self.font_family_var.trace_add("write", self._on_font_change)
        # self.font_size_var.trace_add("write", self._on_font_change) # Removed as font size is now per-column

    def _build_dynamic_coord_controls(self):
        # Clear existing controls
        for widget in self.column_controls_sidebar.winfo_children():
            widget.destroy()
        
        self.is_rtl_vars = []
        self.col_status_vars = []
        # self.col_alignment_vars is re-initialized in load_excel_data or when managed_columns changes
        self.col_font_size_vars = []
        self.col_alignment_vars = []

        if self.signature_mode_active.get():
            # --- Section 1: Load New Signature Button ---
            load_button_frame = customtkinter.CTkFrame(self.column_controls_sidebar, fg_color="transparent")
            load_button_frame.pack(fill=tk.X, pady=5, padx=5)
            customtkinter.CTkButton(load_button_frame, text="Load New Signature Image", command=self.load_signature_image_prompt).pack(fill=tk.X)

            # --- Section 2: Available Signatures (Loaded but not yet placed) ---
            customtkinter.CTkLabel(self.column_controls_sidebar, text="Available for Placing:", anchor="w").pack(fill=tk.X, pady=(10,2), padx=5)
            available_list_container = customtkinter.CTkFrame(self.column_controls_sidebar, border_width=1) # Replaces bd/relief
            available_list_container.pack(fill=tk.X, padx=5, pady=(0,10))
            
            if not self.loaded_signature_pil_images:
                customtkinter.CTkLabel(available_list_container, text="(None loaded)").pack(pady=5)
            else:
                for idx, (_, _, display_name) in enumerate(self.loaded_signature_pil_images):
                    f_avail = customtkinter.CTkFrame(available_list_container, fg_color="transparent")
                    f_avail.pack(fill=tk.X, padx=2, pady=1)
                    
                    # Determine fg_color for the label or its frame based on selection
                    # CTk uses fg_color for background. Default is transparent for labels unless set.
                    # Use a theme-aware selection color or a neutral one.
                    # For instance, using a slightly darker shade of the default button color when selected.
                    # Or a specific color that works well in both light/dark modes.
                    ctk_bg_color = customtkinter.ThemeManager.theme["CTkButton"]["fg_color"] if idx == self.active_signature_pil_idx_to_place.get() else "transparent"
                    f_avail.configure(fg_color=ctk_bg_color)
                    
                    avail_label_text = f"{idx+1}. {display_name[:20]}{'...' if len(display_name) > 20 else ''}"
                    # Label itself should be transparent to show frame's color
                    avail_label = customtkinter.CTkLabel(f_avail, text=avail_label_text, anchor="w", padx=3, fg_color="transparent")
                    avail_label.pack(side=tk.LEFT, fill=tk.X, expand=True)
                    avail_label.bind("<Button-1>", lambda e, i=idx: self._set_active_signature_for_placing(i))

            # --- Section 2.5: Delete Selected Signature Button (if a signature is selected) ---
            if self.selected_placed_signature_idx.get() != -1:
                delete_button_frame = customtkinter.CTkFrame(self.column_controls_sidebar, fg_color="transparent")
                delete_button_frame.pack(fill=tk.X, pady=(10,0), padx=5)
                customtkinter.CTkButton(delete_button_frame, text="Delete Selected", command=self.delete_selected_placed_signature, fg_color="salmon", text_color="black", hover_color="#E07A70").pack(fill=tk.X)
            
            # --- Section 3: Placed Signatures on Document ---
            customtkinter.CTkLabel(self.column_controls_sidebar, text="Placed on Document:", anchor="w").pack(fill=tk.X, pady=(10,2), padx=5)
            selected_placed_idx = self.selected_placed_signature_idx.get()
            for idx, sig_data_item in enumerate(self.placed_signatures_data):
                pil_image_idx = sig_data_item['pil_image_idx']
                _, _, display_name = self.loaded_signature_pil_images[pil_image_idx]
                
                item_frame = customtkinter.CTkFrame(self.column_controls_sidebar, border_width=1) # Replaces bd/relief
                item_frame.pack(fill=tk.X, padx=5, pady=3)
                if idx == selected_placed_idx:
                    # Use a theme-aware selection color
                    item_frame.configure(fg_color=customtkinter.ThemeManager.theme["CTkButton"]["hover_color"]) # Highlight selected

                label_text = f"Sig {idx + 1}: {display_name[:15]}{'...' if len(display_name) > 15 else ''}" # Truncate name
                customtkinter.CTkLabel(item_frame, text=label_text, anchor="w", fg_color="transparent").pack(side=tk.LEFT, padx=(2,5), fill=tk.X, expand=True)
                
                customtkinter.CTkButton(item_frame, text="Del", command=lambda i=idx: self._handle_sidebar_delete_signature(i), width=35).pack(side=tk.RIGHT, padx=(0,2))
                customtkinter.CTkButton(item_frame, text="Sel", command=lambda i=idx: self._handle_sidebar_select_signature(i), width=35).pack(side=tk.RIGHT, padx=(0,2))
            
            if not self.placed_signatures_data:
                 customtkinter.CTkLabel(self.column_controls_sidebar, text="(None placed on document)", anchor="center").pack(pady=10, fill=tk.X)


        else: # Text injection mode
            if not self.managed_columns: # Check if there are any managed columns (original or duplicated)
                customtkinter.CTkLabel(self.column_controls_sidebar, text="Load Excel file\nto define text fields.", anchor="center").pack(pady=20, fill=tk.X)
                return

            for managed_idx, mc_data in enumerate(self.managed_columns):
                # Ensure control variable lists are long enough. This should be handled by duplicate_managed_column.
                # For initial build after Excel load, they are sized correctly.
                # This is more of a safeguard or for clarity.
                while len(self.is_rtl_vars) <= managed_idx: self.is_rtl_vars.append(tk.BooleanVar(value=True))
                while len(self.col_alignment_vars) <= managed_idx: self.col_alignment_vars.append(tk.StringVar(value=TEXT_ALIGNMENTS[0]))
                while len(self.col_status_vars) <= managed_idx: self.col_status_vars.append(tk.StringVar(value="✖"))
                while len(self.col_font_size_vars) <= managed_idx: self.col_font_size_vars.append(tk.IntVar(value=12)) # Default font size

                rtl_var = tk.BooleanVar(value=True) # Default to True for Hebrew context
                rtl_var.trace_add("write", self._on_font_change) # Update preview on change
                self.is_rtl_vars[managed_idx] = rtl_var # Assign to the correct index
                
                alignment_var = tk.StringVar(value=TEXT_ALIGNMENTS[0]) # Default to "left"
                alignment_var.trace_add("write", self._on_font_change)
                self.col_alignment_vars[managed_idx] = alignment_var
                
                font_size_var = tk.IntVar(value=self.managed_columns[managed_idx].get('font_size', 12)) # Get from managed_columns or default
                font_size_var.trace_add("write", self._on_font_change)
                self.col_font_size_vars[managed_idx] = font_size_var


                status_var = tk.StringVar(value="✖") # Default to not placed
                if managed_idx < len(self.coords_pdf) and self.coords_pdf[managed_idx] is not None and self.coords_pdf[managed_idx].get('coord') is not None:
                    page_num_for_status = self.coords_pdf[managed_idx]['page_num']
                    status_var.set(f"✔ (P.{page_num_for_status + 1})") # Set to placed if coord exists
                else:
                    status_var.set("✖")
                self.col_status_vars[managed_idx] = status_var

                item_frame = customtkinter.CTkFrame(self.column_controls_sidebar, border_width=1) # Replaces bd/relief
                item_frame.pack(fill=tk.X, padx=5, pady=3)

                # Frame for left-aligned items (Status and Name)
                left_aligned_frame = customtkinter.CTkFrame(item_frame, fg_color="transparent")
                left_aligned_frame.pack(side=tk.LEFT, padx=(0,5), fill=tk.X, expand=True) # Allow this to expand to push right frame

                customtkinter.CTkLabel(left_aligned_frame, textvariable=status_var, width=25, font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=(2,0))
                name_label = customtkinter.CTkLabel(left_aligned_frame, text=f"{mc_data['display_name']}:", anchor="w")
                # Let name_label fill available space in the left_aligned_frame
                name_label.pack(side=tk.LEFT, padx=(0,5), fill=tk.X, expand=True)

                # Frame for right-aligned items (all other controls)
                right_aligned_frame = customtkinter.CTkFrame(item_frame, fg_color="transparent")
                right_aligned_frame.pack(side=tk.RIGHT, padx=(5,0))

                # Pack controls into right_aligned_frame, from left to right for their internal order
                customtkinter.CTkCheckBox(right_aligned_frame, text="RTL", variable=rtl_var, width=45).pack(side=tk.LEFT, padx=(0,3))
                align_button = customtkinter.CTkSegmentedButton(right_aligned_frame, values=TEXT_ALIGNMENTS, variable=alignment_var, width=90, height=28) # Further reduced width
                align_button.pack(side=tk.LEFT, padx=(0,3))
                customtkinter.CTkLabel(right_aligned_frame, text="Size:").pack(side=tk.LEFT, padx=(3,1)) # Abbreviated "Size"
                customtkinter.CTkEntry(right_aligned_frame, textvariable=font_size_var, width=28).pack(side=tk.LEFT, padx=(0,1)) # Reduced width
                customtkinter.CTkButton(right_aligned_frame, text="-", command=lambda mi=managed_idx: self._adjust_specific_font_size(mi, -1), width=16).pack(side=tk.LEFT, padx=(0,1)) # Reduced width
                customtkinter.CTkButton(right_aligned_frame, text="+", command=lambda mi=managed_idx: self._adjust_specific_font_size(mi, 1), width=16).pack(side=tk.LEFT, padx=(0,3)) # Reduced width
                customtkinter.CTkButton(right_aligned_frame, text="Move", command=lambda mi=managed_idx: self.prepare_to_set_coord(mi), width=40).pack(side=tk.LEFT, padx=(0,2)) # Reduced width
                customtkinter.CTkButton(right_aligned_frame, text="Dup", command=lambda mi=managed_idx: self.duplicate_managed_column(mi), width=35).pack(side=tk.LEFT, padx=(0,2)) # Reduced width


    def _handle_sidebar_select_signature(self, sig_idx):
        self._select_placed_signature(sig_idx)

    def _handle_sidebar_delete_signature(self, sig_idx):
        self.selected_placed_signature_idx.set(sig_idx) # Set as selected for deletion logic
        self.delete_selected_placed_signature()

    def _set_active_signature_for_placing(self, pil_idx):
        if 0 <= pil_idx < len(self.loaded_signature_pil_images):
            self.active_signature_pil_idx_to_place.set(pil_idx)
            self.status_label.configure(text=f"Ready to place: {self.loaded_signature_pil_images[pil_idx][2]}. Click on PDF.")
            self._build_dynamic_coord_controls() # Refresh sidebar to show selection

    def _on_font_change(self, *args):
        if self.is_text_preview_active and not self.signature_mode_active.get():
            self._update_text_preview()

    def _adjust_specific_font_size(self, managed_idx, delta):
        if not (0 <= managed_idx < len(self.col_font_size_vars)):
            return
        try:
            current_size = self.col_font_size_vars[managed_idx].get()
            new_size = current_size + delta
            if new_size >= 1: # Ensure font size is at least 1
                self.col_font_size_vars[managed_idx].set(new_size)
                self.managed_columns[managed_idx]['font_size'] = new_size # Update stored value
        except tk.TclError: # Handle cases where entry might be temporarily invalid
            pass

    def prepare_to_set_coord(self, managed_col_idx):
        if self.pdf_doc:
            self.active_coord_to_set_idx = managed_col_idx # This is the index in self.managed_columns
            display_name = self.managed_columns[managed_col_idx]['display_name']
            self.status_label.configure(text=f"Select position for '{display_name}' on the image, or drag the marker.")
            self._drag_data["item"] = None
            # If text preview is active, update it to potentially clear old highlights or focus
            if self.is_text_preview_active:
                self._update_text_preview()
        else:
            self.status_label.configure(text="Please load a PDF file first.")

    def duplicate_managed_column(self, managed_idx_to_duplicate):
        if not (0 <= managed_idx_to_duplicate < len(self.managed_columns)):
            return

        original_mc_data = self.managed_columns[managed_idx_to_duplicate]
        original_excel_idx = original_mc_data['original_excel_col_idx']

        # Find existing copy count for this original_excel_idx
        # Use the original header value (or default "Col N") for the copy name base
        # This original_header_value is essentially original_mc_data['display_name'] if it's an original column,
        # or the base part of it if it's already a copy.
        # For simplicity, we'll use the display name of the item being duplicated as the base for the new copy name.
        base_name_for_copy = original_mc_data['display_name']
        # If base_name_for_copy already is a copy, strip the "(Copy N)" part to get the true base
        if "(Copy " in base_name_for_copy and base_name_for_copy.endswith(")"):
            base_name_for_copy = base_name_for_copy.rsplit(" (Copy ", 1)[0]

        copy_count = 0
        for mc in self.managed_columns:
            if mc['original_excel_col_idx'] == original_excel_idx:
                if "(Copy" in mc['display_name']: # A bit simplistic, assumes "(Copy N)" format
                    copy_count +=1
        new_display_name = f"{base_name_for_copy} (Copy {copy_count + 1})"
        new_unique_id = f"col_{original_excel_idx}_copy_{copy_count + 1}" 
        copied_font_size = self.col_font_size_vars[managed_idx_to_duplicate].get()
        self.managed_columns.append({'original_excel_col_idx': original_excel_idx, 'display_name': new_display_name, 'unique_id': new_unique_id, 'font_size': copied_font_size})
        self.coords_pdf.append(None) # New placement starts as None
        self.is_rtl_vars.append(tk.BooleanVar(value=self.is_rtl_vars[managed_idx_to_duplicate].get())) # Copy RTL
        self.col_alignment_vars.append(tk.StringVar(value=self.col_alignment_vars[managed_idx_to_duplicate].get())) # Copy alignment
        self.col_status_vars.append(tk.StringVar(value="✖"))
        self.col_font_size_vars.append(tk.IntVar(value=copied_font_size)) # Copy font size

        self._build_dynamic_coord_controls()
        self.status_label.configure(text=f"'{new_display_name}' created. Use 'Move' to position it.")
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
        if self.excel_data_preview is not None and not self.excel_data_preview.empty and hasattr(self, 'prev_row_button'): # Ensure buttons exist
            current_idx = self.preview_row_index.get()
            num_rows = self.excel_data_preview.shape[0]
            self.preview_row_display.set(f"Row: {current_idx + 1}/{num_rows}")

            self.prev_row_button.configure(state=tk.NORMAL if current_idx > 0 else tk.DISABLED)
            self.next_row_button.configure(state=tk.NORMAL if current_idx < num_rows - 1 else tk.DISABLED)
        else:
            self.preview_row_display.set("Row: -")
            self.prev_row_button.configure(state=tk.DISABLED)
            self.next_row_button.configure(state=tk.DISABLED)

    def _handle_mouse_wheel_zoom(self, event):
        # Cancel any pending zoom operation
        if self._zoom_debounce_timer is not None:
            self.master.after_cancel(self._zoom_debounce_timer)

        # Schedule the zoom operation
        self._zoom_debounce_timer = self.master.after(self._DEBOUNCE_TIME_MS, lambda e=event: self._perform_zoom_from_wheel(e))

    def _perform_zoom_from_wheel(self, event):
        """This method is called after the debounce delay."""
        self._zoom_debounce_timer = None # Reset timer ID

        if not self.pdf_doc:
            return

        # Get mouse position on canvas (relative to the top-left of the scrollable content)
        # and widget coordinates (relative to the canvas widget itself)
        mouse_x_img_old = self.canvas.canvasx(event.x)
        mouse_y_img_old = self.canvas.canvasy(event.y)

        factor_change = 0
        # Respond to Linux wheel events
        if event.num == 4: # Scroll up
            factor_change = 0.25 # Increased zoom step
        elif event.num == 5: # Scroll down
            factor_change = -0.25
        # Respond to Windows/Mac wheel events
        elif event.delta > 0: # Scroll up
            factor_change = 0.25
        elif event.delta < 0: # Scroll down
            factor_change = -0.25
        
        if factor_change != 0:
            # Pass mouse coordinates to the zoom function
            self.zoom(factor_change, mouse_x_img_old, mouse_y_img_old, event.x, event.y)

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
        elif potential_new_zoom > 10.0: # Increased max zoom from 5.0 to 10.0
            new_zoom = 10.0
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
        
        # CRITICAL: Update self.pdf_page_width_pt and self.pdf_page_height_pt to current page's dimensions
        self.pdf_page_width_pt = page.rect.width
        self.pdf_page_height_pt = page.rect.height

        # Get actual canvas dimensions
        canvas_actual_width = self.canvas.winfo_width()
        canvas_actual_height = self.canvas.winfo_height()

        # Determine the drawing position and scrollregion
        # If image is smaller than canvas, center it and make scrollregion same as canvas.
        # If image is larger, draw at 0,0 of scrollregion and make scrollregion same as image.
        
        draw_x = 0
        draw_y = 0
        scroll_w = self.image_on_canvas_width_px
        scroll_h = self.image_on_canvas_height_px

        if self.image_on_canvas_width_px < canvas_actual_width:
            draw_x = (canvas_actual_width - self.image_on_canvas_width_px) // 2
            scroll_w = canvas_actual_width
        if self.image_on_canvas_height_px < canvas_actual_height:
            draw_y = (canvas_actual_height - self.image_on_canvas_height_px) // 2
            scroll_h = canvas_actual_height

        self.photo_image = tk.PhotoImage(data=pix.tobytes("ppm"))
        self.canvas.delete("pdf_image") # Delete only the old PDF image
        self.canvas.create_image(draw_x, draw_y, anchor=tk.NW, image=self.photo_image, tags="pdf_image")
        
        self.canvas.config(scrollregion=(0, 0, scroll_w, scroll_h))

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
        current_page_on_canvas = self.current_pdf_page_num.get()

        # Iterate through managed_columns, as coords_pdf is indexed by managed_idx
        for managed_idx in range(len(self.managed_columns)):
            if managed_idx < len(self.coords_pdf): # Ensure coords_pdf has an entry for this managed_idx
                coord_data = self.coords_pdf[managed_idx]
                if coord_data and coord_data.get('coord') and coord_data.get('page_num') == current_page_on_canvas:
                    pdf_coord_tuple = coord_data['coord']
                    relative_canvas_coords = self._pdf_coords_to_relative_canvas_coords(pdf_coord_tuple)
                    if relative_canvas_coords:
                        pdf_image_x_offset, pdf_image_y_offset = self._get_pdf_image_offset_on_canvas()
                        abs_canvas_x = relative_canvas_coords[0] + pdf_image_x_offset
                        abs_canvas_y = relative_canvas_coords[1] + pdf_image_y_offset

                        # Color based on original_excel_col_idx for consistency if columns are duplicated
                        original_excel_idx = self.managed_columns[managed_idx]['original_excel_col_idx']
                        color = MARKER_COLORS[original_excel_idx % len(MARKER_COLORS)]
                        
                        marker_tag = f"marker_{managed_idx}" # Tag uses managed_idx
                        self.canvas.create_rectangle(
                            abs_canvas_x - marker_radius, abs_canvas_y - marker_radius,
                            abs_canvas_x + marker_radius, abs_canvas_y + marker_radius,
                            fill=color, outline=color, tags=(marker_tag, "marker")
                        )


    def _get_pdf_image_offset_on_canvas(self):
        """Returns the (x, y) offset of the 'pdf_image' item on the canvas."""
    def _draw_placed_signatures(self):
        self.canvas.delete("signature_instance") # Delete all signature instances
        if not self.signature_mode_active.get() or not self.pdf_doc:
            return

        for idx, sig_data in enumerate(self.placed_signatures_data):
            # Get relative canvas parameters (x,y,w,h) for the signature
            relative_canvas_params = self._pdf_rect_to_relative_canvas_rect_params(sig_data['pdf_rect_pts'])
            if relative_canvas_params:
                rel_canvas_x, rel_canvas_y, canvas_w, canvas_h = relative_canvas_params

                # Add the offset of the PDF image on the canvas
                pdf_image_x_offset, pdf_image_y_offset = self._get_pdf_image_offset_on_canvas()
                abs_canvas_x = rel_canvas_x + pdf_image_x_offset
                abs_canvas_y = rel_canvas_y + pdf_image_y_offset
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
                sig_data['canvas_item_id'] = self.canvas.create_image(abs_canvas_x, abs_canvas_y, anchor=tk.NW, image=sig_data['tk_photo'], tags=("signature_instance", f"sig_{idx}"))
        # Selection highlights are now handled exclusively by _redraw_selection_highlights()
        self._redraw_selection_highlights() # Ensure highlights are correct after redrawing all signatures

    def _get_pdf_image_offset_on_canvas(self):
        """Returns the (x, y) offset of the 'pdf_image' item on the canvas."""
        pdf_image_items = self.canvas.find_withtag("pdf_image")
        if pdf_image_items:
            coords = self.canvas.coords(pdf_image_items[0])
            if coords:
                return coords[0], coords[1] # x, y of the top-left corner
        return 0, 0 # Default if not found or no coords

    def _pdf_coords_to_relative_canvas_coords(self, pdf_coords_tuple):
        """Converts PDF coordinates to canvas coordinates RELATIVE to the PDF image's top-left corner."""
        if not self.pdf_doc or self.pdf_page_width_pt == 0 or self.pdf_page_height_pt == 0:
            return None
        pdf_x_pt, pdf_y_pt_from_bottom = pdf_coords_tuple

        # Convert PDF coordinates (origin bottom-left) to canvas image coordinates (origin top-left)
        canvas_x_on_image = (pdf_x_pt / self.pdf_page_width_pt) * self.image_on_canvas_width_px
        
        # PDF Y is from bottom, Canvas Y is from top.
        # So, (1 - (pdf_y / pdf_height)) gives the proportional distance from the top of the PDF.
        canvas_y_on_image = (1 - (pdf_y_pt_from_bottom / self.pdf_page_height_pt)) * self.image_on_canvas_height_px

        return (canvas_x_on_image, canvas_y_on_image)

    def _canvas_coords_to_pdf_coords(self, abs_canvas_x, abs_canvas_y):
        """Converts absolute canvas click coordinates to PDF points (bottom-left origin)."""
        if not self.pdf_doc or self.image_on_canvas_width_px == 0 or self.image_on_canvas_height_px == 0:
            return None

        pdf_image_x_offset, pdf_image_y_offset = self._get_pdf_image_offset_on_canvas()
        # Convert absolute canvas coords to coords relative to the PDF image
        relative_canvas_x = abs_canvas_x - pdf_image_x_offset
        relative_canvas_y = abs_canvas_y - pdf_image_y_offset

        # Now use the existing logic with relative coordinates
        return self._relative_canvas_coords_to_pdf_coords(relative_canvas_x, relative_canvas_y)

    def load_pdf_template(self):
        path = filedialog.askopenfilename(
            title="Select PDF File",
            filetypes=(("PDF files", "*.pdf"), ("All files", "*.*"))
        )
        if not path:
            return

        self.pdf_path.set(path)
        filename = os.path.basename(path) if path else "(No file selected)"
        self.pdf_display_var.set(filename)
        # For CTkEntry, if state is disabled, we might need to temporarily enable to set, then disable
        # self.pdf_display_entry.configure(state="normal")
        # self.pdf_display_entry.delete(0, tk.END)
        # self.pdf_display_entry.insert(0, filename)
        # self.pdf_display_entry.configure(state="disabled")
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
            self.pdf_nav_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(0,2)) # Show nav controls within right_pdf_panel

            # Mode is now user-selected, but we still need to refresh UI elements that depend on PDF load
            self._on_signature_mode_change() # Refresh UI based on current mode

            # Calculate initial zoom to fit page height
            self.master.update_idletasks() # Ensure canvas dimensions are up-to-date
            canvas_height_available = self.canvas.winfo_height()
            
            if self.pdf_page_height_pt > 0 and canvas_height_available > 10: # Avoid division by zero or tiny canvas
                # Subtract a small margin for scrollbars or padding if necessary
                effective_canvas_height = canvas_height_available - 5 # Small margin
                zoom_to_fit_height = effective_canvas_height / self.pdf_page_height_pt
                
                # Clamp new_zoom to min/max values (same as in self.zoom)
                new_initial_zoom = max(0.2, min(zoom_to_fit_height, 5.0))
                self.current_zoom_factor.set(round(new_initial_zoom, 2))
            else:
                self.current_zoom_factor.set(1.0) # Default to 100% if calculation is not possible
            self.zoom_display_var.set(f"Zoom: {int(self.current_zoom_factor.get() * 100)}%")

            self._redisplay_pdf_page(page_number=0) # Display first page
            
            if not self.signature_mode_active.get():
                if self.num_excel_cols > 0: # Excel is loaded
                    self.status_label.configure(text=f"PDF loaded. Click 'Move' for a field, or click PDF for next unplaced.")
                    if self.is_text_preview_active and any(item is not None and item.get('coord') is not None for item in self.coords_pdf):
                         self._update_text_preview()
                else:
                    self.status_label.configure(text="PDF file loaded. Load an Excel file to define text fields.")
            # else: status already set by _on_signature_mode_change
            
            # No specific column is being set by "Move" button initially
            # self.active_coord_to_set_idx = None # This is already the default
            if not self.signature_mode_active.get():
                self._update_text_preview() # Will clear if coords are None
            
        except Exception as e:
            messagebox.showerror("Error Loading PDF", str(e))
            self.pdf_doc = None
            error_msg = "(Error loading)"
            self.pdf_display_var.set(error_msg)
            # self.pdf_display_entry.configure(state="normal")
            # self.pdf_display_entry.delete(0, tk.END)
            # self.pdf_display_entry.insert(0, error_msg)
            # self.pdf_display_entry.configure(state="disabled")
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
        filename = os.path.basename(path) if path else "(No file selected)"
        self.excel_display_var.set(filename)
        # self.excel_display_entry.configure(state="normal")
        # self.excel_display_entry.delete(0, tk.END)
        # self.excel_display_entry.insert(0, filename)
        # self.excel_display_entry.configure(state="disabled")

        try:
            df = pd.read_excel(path, header=None) # Assume no header for simplicity, take first two columns
            if df.empty or df.shape[1] == 0:
                messagebox.showerror("Error", "The Excel file is empty or contains no columns.")
                self.excel_path.set("")
                self.num_excel_cols = 0
                error_msg = "(Empty or invalid file)"
                self.excel_display_var.set(error_msg)
                # self.excel_display_entry.configure(state="normal"); self.excel_display_entry.delete(0, tk.END); self.excel_display_entry.insert(0, error_msg); self.excel_display_entry.configure(state="disabled")

                self.coords_pdf = []
                self.managed_columns.clear()
                return
            
            self.num_excel_cols = df.shape[1] # Number of original Excel columns
            
            # Get header values from the first row for display names
            header_values = []
            if not df.empty and df.shape[0] > 0: # Check if there's at least one row
                header_values = [str(df.iloc[0, i]) if pd.notna(df.iloc[0, i]) else "" for i in range(self.num_excel_cols)]
            else: # If Excel is empty or has no rows
                 header_values = [""] * self.num_excel_cols # Empty headers if no data rows

            # Initialize managed_columns based on original Excel columns
            self.managed_columns.clear()
            for i in range(self.num_excel_cols):
                display_name = header_values[i] if header_values[i] else f"Col {i+1}" # Use header or default
                self.managed_columns.append({
                    'original_excel_col_idx': i,
                    'display_name': display_name,
                    'unique_id': f"col_{i}_orig", 
                    'font_size': 12 # Default font size for new columns
                })

            self.coords_pdf = [None] * len(self.managed_columns)
            # Initialize status vars when Excel is loaded
            self.col_status_vars = [tk.StringVar(value="✖") for _ in range(len(self.managed_columns))] # Already done in _build_dynamic_coord_controls
            self.col_alignment_vars = [tk.StringVar(value=TEXT_ALIGNMENTS[0]) for _ in range(len(self.managed_columns))]
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
                 self.status_label.configure(text=f"Excel loaded ({len(self.managed_columns)} fields). Click PDF for next unplaced, or use 'Move'.")
            else:
                 self.status_label.configure(text=f"Excel loaded ({len(self.managed_columns)} fields). Load PDF to start.")
            self.excel_data_preview = df
            self.preview_row_index.set(0) 
            self._update_preview_row_display_and_buttons() # Update buttons AFTER df is set
            # Try to update preview if PDF is also loaded and at least one coord is set
            if self.is_text_preview_active and self.pdf_doc and any(item is not None and item.get('coord') is not None for item in self.coords_pdf):
                 self._update_text_preview()
        except Exception as e:
            messagebox.showerror("Error Loading Excel", str(e))
            self.excel_path.set("")
            error_msg = "(Error loading)"
            self.excel_display_var.set(error_msg)
            # self.excel_display_entry.configure(state="normal"); self.excel_display_entry.delete(0, tk.END); self.excel_display_entry.insert(0, error_msg); self.excel_display_entry.configure(state="disabled")
            self.excel_preview_text.set("Excel Preview: (Error loading)")
            self.managed_columns.clear()
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
        dirname = os.path.basename(path) if path else "(No folder selected)"
        self.output_dir_display_var.set(dirname)
        # self.output_dir_display_entry.configure(state="normal")
        # self.output_dir_display_entry.delete(0, tk.END)
        # self.output_dir_display_entry.insert(0, dirname)
        # self.output_dir_display_entry.configure(state="disabled")
        self.status_label.configure(text=f"Output folder selected: {path}")

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

        self.prev_pdf_page_button.configure(state=tk.NORMAL if current_page_0_indexed > 0 else tk.DISABLED)
        self.next_pdf_page_button.configure(state=tk.NORMAL if current_page_0_indexed < total_pages - 1 else tk.DISABLED)

    def _change_pdf_page(self, delta):
        new_page_num = self.current_pdf_page_num.get() + delta
        if 0 <= new_page_num < self.pdf_total_pages.get():
            self.current_pdf_page_num.set(new_page_num)
            self._redisplay_pdf_page(page_number=new_page_num) # This will also call _update_page_nav_controls
    def _canvas_coords_to_pdf_coords(self, abs_canvas_x_param, abs_canvas_y_param): # Renamed params to avoid conflict
        """Converts absolute canvas click coordinates to PDF points (bottom-left origin)."""
        if not self.pdf_doc or self.image_on_canvas_width_px == 0 or self.image_on_canvas_height_px == 0:
            return None

        pdf_image_x_offset, pdf_image_y_offset = self._get_pdf_image_offset_on_canvas()
        # Convert absolute canvas coords to coords relative to the PDF image
        relative_canvas_x = abs_canvas_x_param - pdf_image_x_offset
        relative_canvas_y = abs_canvas_y_param - pdf_image_y_offset

        # Now use the existing logic with relative coordinates
        return self._relative_canvas_coords_to_pdf_coords(relative_canvas_x, relative_canvas_y)

    def _relative_canvas_coords_to_pdf_coords(self, relative_canvas_x, relative_canvas_y):
        """Converts canvas coordinates (relative to PDF image) to PDF points (bottom-left origin)."""
        if not self.pdf_doc or self.image_on_canvas_width_px == 0 or self.image_on_canvas_height_px == 0: # Should be checked by caller
            return None
        prop_x = relative_canvas_x / self.image_on_canvas_width_px
        prop_y = relative_canvas_y / self.image_on_canvas_height_px

        pdf_x_pt = prop_x * self.pdf_page_width_pt # Use original PDF width for calculation
        pdf_y_pt_from_top = prop_y * self.pdf_page_height_pt # Use original PDF height
        pdf_y_pt_from_bottom = self.pdf_page_height_pt - pdf_y_pt_from_top
        return (pdf_x_pt, pdf_y_pt_from_bottom)

    def _on_canvas_b1_press(self, event):
        current_item_tuple = self.canvas.find_withtag(tk.CURRENT)
        if current_item_tuple:
            item_id = current_item_tuple[0]
            tags = self.canvas.gettags(item_id)
            # If a resize handle, signature, or marker is pressed, their specific handlers
            # (_on_resize_handle_press, on_placed_signature_press, on_marker_press)
            # will be called due to their tag bindings and should manage _item_drag_active.
            # This general handler should just yield to them by breaking early.
            if RESIZE_HANDLE_TAG in tags or "signature_instance" in tags or "marker" in tags:
                # print(f"DEBUG: _on_canvas_b1_press: Clicked on interactive item with tags {tags}. Returning break.")
                return "break"

        # If we reach here, the click was on the canvas background, not an interactive item.
        # Proceed with canvas pan or click-to-place logic.
        if not self.pdf_doc:
            self.status_label.configure(text="Please load a PDF file first.")
            return "break" # Still break if no PDF, to prevent errors

        # Store press coordinates and prepare for potential pan
        self._pan_data["press_x"] = self.canvas.canvasx(event.x) # Use canvas coords
        self._pan_data["press_y"] = self.canvas.canvasy(event.y) # Use canvas coords
        self._pan_data["is_potential_pan_or_click"] = True
        self._pan_data["has_dragged_for_pan"] = False
        self.canvas.scan_mark(event.x, event.y) # For scan_dragto, event.x/y is fine
        # No "break" here for canvas background click, allow event to propagate if needed by Tkinter's default mechanisms.

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
            pdf_pos_result = self._canvas_pos_to_pdf_pos_tl(current_mouse_x_canvas, current_mouse_y_canvas)
            if pdf_pos_result is None: 
                return "break" # Mouse is outside the PDF image area, do nothing further for resize.
            current_mouse_pdf_x, current_mouse_pdf_y = pdf_pos_result

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
            # If an item drag (marker or signature move) is active,
            # this general canvas motion handler should cede control entirely
            # to the tag-specific motion handlers (e.g., on_marker_motion).
            # Returning "break" ensures that canvas panning logic below is not executed
            # and that the event is consumed, preventing default canvas behaviors.
            return "break"
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
                 self.status_label.configure(text=f"Signature {sig_idx+1} resized.")
            
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

            # Reset pan_data for the next B1 interaction on the canvas (moved down)
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
            if self.managed_columns and self.coords_pdf: # Check against managed_columns
                # Find first unassigned coordinate (where item is None or item['coord'] is None)
                next_unassigned_idx = -1
                for i, item_data in enumerate(self.coords_pdf): # Iterate through coords_pdf (which matches managed_columns length)
                    if item_data is None or item_data.get('coord') is None:
                        next_unassigned_idx = i
                        break
                if next_unassigned_idx != -1:
                    idx_to_update = next_unassigned_idx
                else: # All coordinates are assigned
                    self.status_label.configure(text="All fields positioned. Use 'Move' or 'Dup'.")
                    return # Exit if all are assigned and no specific "Move" was clicked
            else: # No Excel loaded or no columns
                self.status_label.configure(text="Load Excel file to define fields for positioning.")
                return

        if idx_to_update != -1:
            # Convert event coordinates to canvas coordinates (accounts for scrolling)
            canvas_x = self.canvas.canvasx(event.x)
            canvas_y = self.canvas.canvasy(event.y)

            pdf_image_x_offset, pdf_image_y_offset = self._get_pdf_image_offset_on_canvas()
            pdf_image_right_boundary = pdf_image_x_offset + self.image_on_canvas_width_px
            pdf_image_bottom_boundary = pdf_image_y_offset + self.image_on_canvas_height_px

            if not (pdf_image_x_offset <= canvas_x <= pdf_image_right_boundary and \
                    pdf_image_y_offset <= canvas_y <= pdf_image_bottom_boundary):
                self.status_label.configure(text="Click within the image boundaries.")
                return

            pdf_coords = self._canvas_coords_to_pdf_coords(canvas_x, canvas_y)
            if not pdf_coords:
                self.status_label.configure(text="Error calculating coordinates.")
                return

            self.coords_pdf[idx_to_update] = {
                'page_num': self.current_pdf_page_num.get(),
                'coord': pdf_coords
            }
            # Ensure col_status_vars is long enough (it should be if managed_columns is source of truth for length)
            if idx_to_update < len(self.col_status_vars) and idx_to_update < len(self.coords_pdf) and self.coords_pdf[idx_to_update]:
                page_num_for_status = self.coords_pdf[idx_to_update].get('page_num', -1) # Default if somehow missing
                self.col_status_vars[idx_to_update].set(f"✔ (P.{page_num_for_status + 1})")
            
            # Check if there's a next unassigned coordinate
            next_unassigned_idx_for_status = -1
            for i, item_data in enumerate(self.coords_pdf): # Re-check after update
                if item_data is None or item_data.get('coord') is None:
                    next_unassigned_idx_for_status = i
                    break
            
            current_page_for_status = self.current_pdf_page_num.get() + 1
            field_display_name = self.managed_columns[idx_to_update]['display_name']
            status_msg = f"'{field_display_name}' positioned on P.{current_page_for_status}. "
            self.status_label.configure(text=status_msg + (f"Click to position next unplaced field." if next_unassigned_idx_for_status != -1 else "All fields positioned."))
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
            self.status_label.configure(text="Please select a signature image from the list to place.")
            return

        canvas_x_click = self.canvas.canvasx(event.x)
        canvas_y_click = self.canvas.canvasy(event.y)

        if not (0 <= canvas_x_click <= self.image_on_canvas_width_px and \
                0 <= canvas_y_click <= self.image_on_canvas_height_px):
            self.status_label.configure(text="Please click within the image boundaries.")
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
        
        self.status_label.configure(text=f"Signature '{display_name}' added. Click to select or drag.")
    
    def on_marker_press(self, event):
        item = self.canvas.find_withtag(tk.CURRENT) # Get item under cursor
        if not item:
            return
        item_id = item[0]
        tags = self.canvas.gettags(item_id)

        # col_idx here refers to managed_idx
        managed_idx_pressed = -1
        for tag in tags:
            if tag.startswith("marker_"):
                try:
                    managed_idx_pressed = int(tag.split("_")[1])
                    break
                except ValueError:
                    continue
        if managed_idx_pressed == -1:
             return # Not a marker we are interested in
        col_idx = managed_idx_pressed # Use clearer variable name

        self._drag_data["item"] = item_id # This is the canvas item_id of the marker
        self._drag_data["col_idx"] = col_idx
        self._drag_data["x"] = self.canvas.canvasx(event.x)
        self._drag_data["y"] = self.canvas.canvasy(event.y)
        self.active_coord_to_set_idx = None # Cancel click-to-set mode
        self._item_drag_active = True # Signal that an item drag has started

        # Find all items belonging to this marker group (text and rectangle)
        specific_tag_for_group = f"marker_{managed_idx_pressed}"
        items_in_group = self.canvas.find_withtag(specific_tag_for_group)
        self._drag_data["items_to_move_together"] = list(items_in_group)

    def on_marker_motion(self, event):
        # print(f"DEBUG MARKER MOTION: drag_data={self._drag_data}")
        if not self._drag_data["item"]:
            return # No item being dragged

        current_x = self.canvas.canvasx(event.x)
        current_y = self.canvas.canvasy(event.y)
        
        dx = current_x - self._drag_data["x"]
        dy = current_y - self._drag_data["y"]

        # Move all items in the group
        items_to_move = self._drag_data.get("items_to_move_together")
        if items_to_move:
            for item_id_in_group in items_to_move:
                self.canvas.move(item_id_in_group, dx, dy)
        else: # Fallback if items_to_move_together was not set (should not happen)
            self.canvas.move(self._drag_data["item"], dx, dy)
            
        self._drag_data["x"] = current_x
        self._drag_data["y"] = current_y

        # Update PDF coordinates
        # Get the canvas coordinates of the dragged item's reference point
        item_id_dragged = self._drag_data["item"]
        marker_coords_canvas = self.canvas.coords(item_id_dragged)
        item_type = self.canvas.type(item_id_dragged)

        new_canvas_ref_x, new_canvas_ref_y = 0, 0
        if item_type == "text":
            # For text, coords are [x, y] of the anchor point
            new_canvas_ref_x = marker_coords_canvas[0]
            new_canvas_ref_y = marker_coords_canvas[1]
        elif item_type == "rectangle":
            # For rectangle, calculate center
            new_canvas_ref_x = (marker_coords_canvas[0] + marker_coords_canvas[2]) / 2
            new_canvas_ref_y = (marker_coords_canvas[1] + marker_coords_canvas[3]) / 2
        else:
            print(f"Warning: Dragged 'marker' item is of unexpected type: {item_type}")
            return "break"

        pdf_coords = self._canvas_coords_to_pdf_coords(new_canvas_ref_x, new_canvas_ref_y)

        # current_col_idx is managed_idx
        current_managed_idx = self._drag_data.get("col_idx")
        if pdf_coords and current_managed_idx is not None and 0 <= current_managed_idx < len(self.coords_pdf):
            if self.coords_pdf[current_managed_idx] is not None: # Should exist if dragging
                self.coords_pdf[current_managed_idx]['coord'] = pdf_coords
            else: # Should not happen, but as a safeguard, re-initialize with current page
                self.coords_pdf[current_managed_idx] = {'page_num': self.current_pdf_page_num.get(), 'coord': pdf_coords}
            # DO NOT call self._update_text_preview() here. It will be called on release.
            # The text item is moved directly by self.canvas.move().
            
        return "break" # Consume event to prevent canvas pan while dragging marker

    def on_marker_release(self, event):
        if not self._drag_data["item"]:
            return
        # Final update after drag, ensuring the latest position is used
        # This is mostly redundant if on_marker_motion updates correctly, but good for safety
        item_id_released = self._drag_data["item"]
        marker_coords_canvas = self.canvas.coords(item_id_released)
        item_type = self.canvas.type(item_id_released)

        new_canvas_ref_x, new_canvas_ref_y = 0, 0
        if item_type == "text":
            new_canvas_ref_x = marker_coords_canvas[0]
            new_canvas_ref_y = marker_coords_canvas[1]
        elif item_type == "rectangle":
            new_canvas_ref_x = (marker_coords_canvas[0] + marker_coords_canvas[2]) / 2
            new_canvas_ref_y = (marker_coords_canvas[1] + marker_coords_canvas[3]) / 2
        else:
            # This case should ideally not be reached if press/motion handled it.
            print(f"Warning: Released 'marker' item is of unexpected type: {item_type}")
            self._drag_data.clear()
            self._item_drag_active = False
            return "break"
        pdf_coords = self._canvas_coords_to_pdf_coords(new_canvas_ref_x, new_canvas_ref_y)

        current_managed_idx = self._drag_data.get("col_idx")
        if pdf_coords and current_managed_idx is not None and 0 <= current_managed_idx < len(self.coords_pdf):
            if self.coords_pdf[current_managed_idx] is not None:
                self.coords_pdf[current_managed_idx]['coord'] = pdf_coords
                page_num_for_status = self.coords_pdf[current_managed_idx]['page_num']
                if current_managed_idx < len(self.col_status_vars):
                    self.col_status_vars[current_managed_idx].set(f"✔ (P.{page_num_for_status + 1})")
                field_display_name_drag = self.managed_columns[current_managed_idx]['display_name']
                self.status_label.configure(text=f"'{field_display_name_drag}' position updated on P.{page_num_for_status + 1}.")
            else: # Should not happen
                self.coords_pdf[current_managed_idx] = {'page_num': self.current_pdf_page_num.get(), 'coord': pdf_coords}
                # ... update status var and label ...

        self._drag_data["item"] = None
        self._drag_data["col_idx"] = None
        self._item_drag_active = False # Signal that item drag has ended
        self._drag_data.pop("items_to_move_together", None) # Clean up
        
        if self.is_text_preview_active: # Ensure preview updates on drag release
            self._update_text_preview() # Will iterate through all placements

    def on_marker_double_click(self, event):
        item = self.canvas.find_withtag(tk.CURRENT) # Get item under cursor
        if not item:
            return
        item_id = item[0]
        tags = self.canvas.gettags(item_id)

        managed_idx_dc = -1
        for tag in tags:
            if tag.startswith("marker_"):
                try:
                    managed_idx_dc = int(tag.split("_")[1])
                    break
                except ValueError:
                    continue
        
        if managed_idx_dc != -1 and 0 <= managed_idx_dc < len(self.is_rtl_vars): # Check if managed_idx_dc is valid
            current_rtl_var = self.is_rtl_vars[managed_idx_dc] # Get the BooleanVar for this managed column
            current_rtl_var.set(not current_rtl_var.get())
            # The trace on is_rtl_vars will call _on_font_change, which updates the preview.
            field_display_name_dc = self.managed_columns[managed_idx_dc]['display_name']
            self.status_label.configure(text=f"'{field_display_name_dc}' direction changed to {'RTL' if current_rtl_var.get() else 'LTR'}.")


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
                canvas_params = self._pdf_rect_to_relative_canvas_rect_params(sig_data['pdf_rect_pts'])
                if canvas_params: # These are relative to the PDF image
                    rel_canvas_x, rel_canvas_y, canvas_w, canvas_h = canvas_params
                    
                    # Get the PDF image's offset on the main canvas
                    pdf_image_x_offset, pdf_image_y_offset = self._get_pdf_image_offset_on_canvas()
                    abs_canvas_x = rel_canvas_x + pdf_image_x_offset
                    abs_canvas_y = rel_canvas_y + pdf_image_y_offset
                    self.canvas.create_rectangle(
                        abs_canvas_x, abs_canvas_y, abs_canvas_x + canvas_w, abs_canvas_y + canvas_h,
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
                        (abs_canvas_x, abs_canvas_y, "tl"), (abs_canvas_x + canvas_w, abs_canvas_y, "tr"),
                        (abs_canvas_x + canvas_w, abs_canvas_y + canvas_h, "br"), (abs_canvas_x, abs_canvas_y + canvas_h, "bl")
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
            self.status_label.configure(text=f"Signature moved. Width: {sig_data['pdf_rect_pts'].width:.1f}, Height: {sig_data['pdf_rect_pts'].height:.1f} pt")
        
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
        if not self.coords_pdf or not any(item is not None and item.get('coord') is not None for item in self.coords_pdf):
            if self.managed_columns: # Check if any fields are defined
                messagebox.showwarning("Warning", f"Please select a position for at least one field on the PDF first.")
            else: # Should not happen if Excel is loaded, but as a safeguard
                messagebox.showwarning("Warning", "Please define text fields (load Excel) and select positions.")
            return
        
        # Toggle the state
        new_preview_state = not self.is_text_preview_active
        self.is_text_preview_active = new_preview_state # Set it first
        
        # Then update button text and preview based on the new state
        # (Button text update for Show/Hide can be added here if desired)
        self._update_text_preview() # Will iterate through all placements

    def _update_text_preview(self):
        # Clear existing preview text items
        for item_id in self.preview_text_items:
            self.canvas.delete(item_id)
        self.preview_text_items.clear()
        if not self.is_text_preview_active or \
           self.signature_mode_active.get() or \
           not self.pdf_doc or (self.excel_data_preview is None or self.excel_data_preview.empty) or \
           not self.coords_pdf or not self.managed_columns: # Check against managed_columns
            return

        current_page_on_canvas = self.current_pdf_page_num.get()
        current_row_idx = self.preview_row_index.get()
        if not (self.excel_data_preview is not None and \
                0 <= current_row_idx < self.excel_data_preview.shape[0]):
            # # print(f"Preview row index {current_row_idx} is out of bounds.") # Debug
            return # Invalid row index for preview
        try:
            font_family = self.font_family_var.get()
            font_family_to_use = font_family

            # Validate font_family_to_use once by trying to create a dummy font object.
            try:
                tkFont.Font(family=font_family_to_use, size=1) # Test creation with a dummy size
            except tk.TclError:
                print(f"Warning: Font family '{font_family_to_use}' not valid for Tkinter. Falling back to Arial.")
                font_family_to_use = "Arial"

            for managed_idx in range(len(self.managed_columns)):
                if not (managed_idx < len(self.coords_pdf) and \
                        managed_idx < len(self.is_rtl_vars) and \
                        managed_idx < len(self.col_alignment_vars) and \
                        managed_idx < len(self.col_font_size_vars)):
                    continue # Should not happen if lists are synced

                coord_data_item = self.coords_pdf[managed_idx]
                original_excel_col_idx = self.managed_columns[managed_idx]['original_excel_col_idx']
                
                # Get per-field font size
                field_font_size_pt = self.col_font_size_vars[managed_idx].get()
                if field_font_size_pt <= 0: continue
                current_zoom = self.current_zoom_factor.get()
                tkinter_preview_font_size_px = max(1, int(field_font_size_pt * TKINTER_FONT_SCALE_FACTOR * current_zoom))

                if coord_data_item and coord_data_item.get('coord') and \
                   coord_data_item.get('page_num') == current_page_on_canvas and \
                   original_excel_col_idx < self.excel_data_preview.shape[1]: # Check against original Excel columns
                    
                    val_preview = str(self.excel_data_preview.iloc[current_row_idx, original_excel_col_idx]) if pd.notna(self.excel_data_preview.iloc[current_row_idx, original_excel_col_idx]) else ""
                    text_for_preview = val_preview 
                    
                    pdf_coord_tuple = coord_data_item['coord']
                    is_rtl_current = self.is_rtl_vars[managed_idx].get()

                else:
                    continue # Skip if data for this column is incomplete

                current_alignment = TEXT_ALIGNMENTS[0] # Default to left
                current_alignment = self.col_alignment_vars[managed_idx].get()

                # Get relative canvas coordinates for the text
                relative_canvas_coords = self._pdf_coords_to_relative_canvas_coords(pdf_coord_tuple)
                if relative_canvas_coords: # Check if conversion was successful
                    pdf_image_x_offset, pdf_image_y_offset = self._get_pdf_image_offset_on_canvas()
                    canvas_coords = (relative_canvas_coords[0] + pdf_image_x_offset, 
                                     relative_canvas_coords[1] + pdf_image_y_offset)
                
                    if current_alignment == "left":
                        anchor_val = tk.SW
                    elif current_alignment == "center":
                        anchor_val = tk.S
                    else: # right
                        anchor_val = tk.SE
                    try:
                        # Configure the font object with the specific size for this field
                        specific_marker_tag = f"marker_{managed_idx}"
                        field_specific_font = tkFont.Font(family=font_family_to_use, size=tkinter_preview_font_size_px)
                        item_id = self.canvas.create_text(canvas_coords[0], canvas_coords[1], text=text_for_preview,
                                                         font=field_specific_font, anchor=anchor_val, fill="purple", tags=("preview_text_item", specific_marker_tag, "marker"))
                        self.preview_text_items.append(item_id)
                    except tk.TclError as font_error:
                        print(f"Error creating Tkinter font '{font_family_to_use}' size {tkinter_preview_font_size_px} for preview: {font_error}")
                            
        except Exception as e:
            print(f"Error updating text preview: {e}") # Log error, don't crash

    def _insert_text_on_pdf_page(self, page, text_value, pdf_coord_tuple, font_family_name, font_file_path, font_size_pt, is_rtl, alignment, fitz_font_object):
        """Helper function to insert text onto a PDF page."""
        if pdf_coord_tuple is None:
            return

        text_to_render = get_display(text_value, base_dir='R' if is_rtl else 'L')
        text_width_pt = fitz_font_object.text_length(text_to_render, fontsize=font_size_pt)

        ref_x_pt = pdf_coord_tuple[0]
        # PyMuPDF's insert_text uses y from top of page.
        # self.coords_pdf stores y from bottom of page.
        insertion_point_y_pt = (page.rect.height - pdf_coord_tuple[1]) - Y_OFFSET_PDF_OUTPUT

        # Calculate final X based on alignment
        if alignment == "left":
            final_x_pt = ref_x_pt
        elif alignment == "center":
            final_x_pt = ref_x_pt - (text_width_pt / 2)
        else: # "right"
            final_x_pt = ref_x_pt - text_width_pt

        page.insert_text((final_x_pt, insertion_point_y_pt),
                           text_to_render,
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

        # Check if all defined columns have coordinates
        all_coords_set = True
        # Check if all *managed* columns have placements
        if self.managed_columns and (not self.coords_pdf or not all(item is not None and item.get('coord') is not None for item in self.coords_pdf)):
            all_coords_set = False # This checks if every entry in coords_pdf (corresponding to a managed_column) is set.
        if not all_coords_set:
            messagebox.showerror("Error", "Please select positions for all text columns defined from Excel.")
            return

        try:
            df = pd.read_excel(self.excel_path.get(), header=None)
            if df.shape[1] != self.num_excel_cols: # Consistency check
                messagebox.showerror("Error", "The number of original columns in the Excel file has changed. Please reload.")
                return

            font_family_selected = self.font_family_var.get()
            # Global font_size removed. Will be per-column.
            if not font_family_selected: # Still need a global font family
                messagebox.showerror("Error", "Please select a global font family.")
                return

            try:
                font_path = fm.findfont(font_family_selected)
            except Exception as e: # More general exception if findfont fails unexpectedly
                messagebox.showerror("Font File Error", f"Could not find the font file for '{font_family_selected}'.\nTry selecting a different font.\nError: {e}")
                self.status_label.configure(text=f"Error: Font file not found for {font_family_selected}")
                return

            # Load font once for metrics and use in insert_text
            try:
                # This fitz_font object is for getting text_length.
                # The actual font size will be passed to insert_text per field.
                fitz_font_for_metrics = fitz.Font(fontname=font_family_selected, fontfile=font_path)
            except Exception as e:
                messagebox.showerror("Font Load Error", f"Could not load the font '{font_family_selected}' from path '{font_path}'.\n{e}")

            self.status_label.configure(text="Processing files...")
            self.master.update_idletasks() # Update GUI
            
            num_files_generated = 0 # Initialize counter for generated files
            # Iterate over rows, skipping the first row if include_header_row is false
            for index, row in df.iterrows():                
                doc_copy = fitz.open(self.pdf_path.get())
                # page_to_modify will be determined per column based on stored page_num

                for managed_idx in range(len(self.managed_columns)):
                    if not (managed_idx < len(self.coords_pdf) and \
                            managed_idx < len(self.is_rtl_vars) and \
                            managed_idx < len(self.col_alignment_vars) and \
                            managed_idx < len(self.col_font_size_vars)):
                        continue # Should not happen

                    original_excel_col_idx = self.managed_columns[managed_idx]['original_excel_col_idx']
                    field_font_size_pt = self.col_font_size_vars[managed_idx].get()
                    coord_data_output = self.coords_pdf[managed_idx]

                    # Skip if this row is the header row and we are excluding it
                    if not self.include_header_row.get() and index == 0:
                         continue
                    if original_excel_col_idx >= row.size or not coord_data_output or not coord_data_output.get('coord'): # Check if column exists in row data and coord is set
                        continue # Skip if data for this column is missing or not configured

                    val = str(row.iloc[original_excel_col_idx]) if pd.notna(row.iloc[original_excel_col_idx]) else ""
                    alignment_output = self.col_alignment_vars[managed_idx].get()
                    is_rtl_output = self.is_rtl_vars[managed_idx].get()
                    
                    page_num_to_modify = coord_data_output['page_num']
                    pdf_coord_to_insert = coord_data_output['coord']
                    page_object_to_modify = doc_copy.load_page(page_num_to_modify)

                    self._insert_text_on_pdf_page(page_object_to_modify,
                                                  val, pdf_coord_to_insert,
                                                  font_family_selected, font_path, field_font_size_pt,
                                                  is_rtl_output, alignment_output, fitz_font_for_metrics)

                output_filename = os.path.join(self.output_dir.get(), f"output_pdf_{index + 1 - (0 if self.include_header_row.get() else 1)}.pdf")
                doc_copy.save(output_filename, garbage=4, deflate=True) # Add save options
                doc_copy.close()
                num_files_generated += 1

            self.status_label.configure(text=f"Finished generating {num_files_generated} PDF files in: {self.output_dir.get()}")
            messagebox.showinfo("Success", f"{num_files_generated} PDF files generated successfully!")

        except Exception as e:
            self.status_label.configure(text="Error during file generation.")
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
        all_coords_set_single = True # Check against all managed columns
        if self.managed_columns and (not self.coords_pdf or not all(item is not None and item.get('coord') is not None for item in self.coords_pdf)):
            all_coords_set_single = False
        if not all_coords_set_single:
            messagebox.showerror("Error", "Please select positions for all text columns defined from Excel.")
            return

        current_row_idx = self.preview_row_index.get()
        if not (0 <= current_row_idx < self.excel_data_preview.shape[0]):
            messagebox.showerror("Error", "Invalid row selected for preview.")
            return
        
        # Prevent generating PDF for header row if it's excluded
        if not self.include_header_row.get() and current_row_idx == 0:
            messagebox.showwarning("Preview PDF Generation", "Header row is excluded from output. PDF for this row will not be generated.")
            return

        font_family_selected = self.font_family_var.get()
        # Global font_size removed.
        if not font_family_selected: # Still need a global font family
            messagebox.showerror("Error", "Please select a global font family.")
            return

        try:
            font_path = fm.findfont(font_family_selected)
            # This fitz_font object is for getting text_length.
            # The actual font size will be passed to insert_text per field.
            fitz_font_for_metrics = fitz.Font(fontname=font_family_selected, fontfile=font_path)
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
            self.status_label.configure(text="Generating current PDF...")
            self.master.update_idletasks()

            row_data = self.excel_data_preview.iloc[current_row_idx]
            doc_copy = fitz.open(self.pdf_path.get())
            # page_to_modify will be determined per column

            for managed_idx in range(len(self.managed_columns)):
                if not (managed_idx < len(self.coords_pdf) and \
                        managed_idx < len(self.is_rtl_vars) and \
                        managed_idx < len(self.col_alignment_vars) and \
                        managed_idx < len(self.col_font_size_vars)):
                    continue

                original_excel_col_idx = self.managed_columns[managed_idx]['original_excel_col_idx']
                field_font_size_pt = self.col_font_size_vars[managed_idx].get()
                coord_data_single = self.coords_pdf[managed_idx]

                # This check is technically redundant due to the one at the start of the function for current_row_idx == 0
                # but kept for safety if logic changes.
                # if not self.include_header_row.get() and current_row_idx == 0: continue
                if original_excel_col_idx >= row_data.size or not coord_data_single or not coord_data_single.get('coord'): # Check if column exists in row data and coord is set
                    continue

                val = str(row_data.iloc[original_excel_col_idx]) if pd.notna(row_data.iloc[original_excel_col_idx]) else ""
                is_rtl_output = self.is_rtl_vars[managed_idx].get()
                alignment_output = self.col_alignment_vars[managed_idx].get()
                
                page_num_to_modify_single = coord_data_single['page_num']
                pdf_coord_to_insert_single = coord_data_single['coord']
                page_object_to_modify_single = doc_copy.load_page(page_num_to_modify_single)

                self._insert_text_on_pdf_page(page_object_to_modify_single,
                                              val, pdf_coord_to_insert_single,
                                              font_family_selected, font_path, field_font_size_pt,
                                              is_rtl_output, alignment_output, fitz_font_for_metrics)

            doc_copy.save(output_filepath, garbage=4, deflate=True)
            doc_copy.close()
            self.status_label.configure(text=f"current PDF saved to: {output_filepath}")
            messagebox.showinfo("Success", f"current PDF saved successfully!")
        except Exception as e:
            self.status_label.configure(text="Error generating current PDF.")
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
            # References to self.loaded_signatures_listbox removed as the listbox itself was removed. # type: ignore
            self.status_label.configure(text=f"Signature image '{display_name}' loaded. Select it and click on the PDF to place.")
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
            self.status_label.configure(text="Signature size updated.")
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
            self.status_label.configure(text="Selected signature deleted.")
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
            self.status_label.configure(text="Creating signed PDF...")
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
            self.status_label.configure(text=f"Signed PDF saved to: {output_filepath}")
            messagebox.showinfo("Success", "Signed PDF created and saved successfully!")

        except Exception as e:
            self.status_label.configure(text="Error creating signed PDF.")
            messagebox.showerror("Error Creating Signed PDF", f"Error creating signed PDF: {e}")

    # Helper for signature rect conversion
    def _pdf_rect_to_relative_canvas_rect_params(self, pdf_rect_pts: fitz.Rect):
        # pdf_rect_pts is {x0,y0,x1,y1} in PDF points, y from top
        # Returns (relative_canvas_x_tl, relative_canvas_y_tl, canvas_w, canvas_h)
        # These are relative to the PDF image's top-left on the canvas.
        if not self.pdf_doc or self.pdf_page_width_pt == 0 or self.pdf_page_height_pt == 0 or \
           self.image_on_canvas_width_px == 0 or self.image_on_canvas_height_px == 0 : # Added check for canvas image dims
            return None

        # No need to get canvas_actual_width/height here, as we are calculating relative to the PDF image itself.
        # The PDF image's dimensions on canvas (self.image_on_canvas_width_px, self.image_on_canvas_height_px)
        # already account for the zoom.

        # Convert PDF top-left to canvas top-left
        canvas_x_tl = (pdf_rect_pts.x0 / self.pdf_page_width_pt) * self.image_on_canvas_width_px
        canvas_y_tl = (pdf_rect_pts.y0 / self.pdf_page_height_pt) * self.image_on_canvas_height_px
        
        # Convert PDF width/height to canvas width/height
        pdf_w = pdf_rect_pts.width
        pdf_h = pdf_rect_pts.height
        canvas_w = (pdf_w / self.pdf_page_width_pt) * self.image_on_canvas_width_px
        canvas_h = (pdf_h / self.pdf_page_height_pt) * self.image_on_canvas_height_px
        
        return canvas_x_tl, canvas_y_tl, canvas_w, canvas_h

    def _canvas_pos_to_pdf_pos_tl(self, abs_canvas_x, abs_canvas_y):
        # Converts an absolute canvas top-left click coordinate to PDF top-left coordinate (points, y from top)
        if not self.pdf_doc or self.image_on_canvas_width_px == 0 or self.image_on_canvas_height_px == 0:
            return None

        pdf_image_x_offset, pdf_image_y_offset = self._get_pdf_image_offset_on_canvas()
        # Convert absolute canvas coords to coords relative to the PDF image
        relative_canvas_x = abs_canvas_x - pdf_image_x_offset
        relative_canvas_y = abs_canvas_y - pdf_image_y_offset

        # Ensure the relative click is within the bounds of the PDF image itself
        if not (0 <= relative_canvas_x <= self.image_on_canvas_width_px and \
                0 <= relative_canvas_y <= self.image_on_canvas_height_px):
            return None # Click was outside the PDF image area on canvas

        pdf_x_pt = (relative_canvas_x / self.image_on_canvas_width_px) * self.pdf_page_width_pt
        pdf_y_pt = (relative_canvas_y / self.image_on_canvas_height_px) * self.pdf_page_height_pt
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
    customtkinter.set_appearance_mode("System")  # Modes: "System" (default), "Dark", "Light"
    customtkinter.set_default_color_theme("blue")  # Themes: "blue" (default), "green", "dark-blue"

    root = customtkinter.CTk()
    
    # Default font for CTk widgets is handled by the theme or can be set per widget.
    # The root.option_add("*Font", default_font) is less common/effective for CTk.
    # If a global font change is desired, it's often done by creating a CTkFont object
    # and passing it to widgets, or by modifying the theme.
 
    app = PDFBatchApp(root)
    root.mainloop()